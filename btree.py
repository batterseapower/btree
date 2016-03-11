#kb_to_bytes = 1024
#mb_to_bytes = 1024 * kb_to_bytes
#gb_to_bytes = 1024 * mb_to_bytes

#key_size_bytes = 100
#value_size_bytes = 100
#page_size_bytes = 4 * kb_to_bytes

#memory_bytes = 4 * gb_to_bytes
#num_keys = 1_000_000_000

import math
import itertools


class Peeking(object):
    def __init__(self, iterator):
        self._iterator = iterator
        self._has_next = None

    def __iter__(self):
        if self._has_next != True:
            return self._iterator
        else:
            return itertools.chain(iter([self._next]), self._iterator)

    def has_next(self):
        if self._has_next is None:
            try:
                self._next = self._iterator.next()
                self._has_next = True
            except StopIteration:
                self._has_next = False

        return self._has_next

    def peek(self):
        if self.has_next():
            return self._next
        else:
            raise StopIteration()

    def next(self):
        if self._has_next is None:
            return self._iterator.next()
        elif self._has_next:
            self._has_next = None
            return self._next
        else:
            raise StopIteration()


# Outputs exactly one item per key:
#   * Prefers the left argument when there is a key conflict.
#   * Assumes input iterators are sorted in strictly increasing order
def merge_iters(xs, ys, key=lambda x: x):
    xs, ys = Peeking(xs), Peeking(ys)
    while xs.has_next() and ys.has_next():
        c = cmp(key(xs.peek()), key(ys.peek()))
        if c == 0:
            yield xs.next()
            ys.next()
        elif c < 0:
            yield xs.next()
        elif c > 0:
            yield ys.next()

    for x in xs:
        yield x

    for y in ys:
        yield y


# Internal nodes a triple of (keys, list of singleton lists of child nodes, internal entries)
# Leaf nodes are dictionaries of bounded size
class ABTree(object):
    def __init__(self, min_outdegree, max_leaf_entries, max_internal_entries):
        self.max_outdegree = min_outdegree * 2 - 1
        self.max_leaf_entries = max_leaf_entries
        self.max_internal_entries = max_internal_entries
        self.root = {}

        self.max_push_down = int(math.ceil((max_internal_entries + 1) / float(self.max_outdegree)))

        if min_outdegree < 2:
            raise ValueError('min_outdegree must be at least 2')
        if max_internal_entries < 0:
            raise ValueError('max_internal_entries must be at least 0')
        if max_leaf_entries < self.max_push_down:
            raise ValueError('max_leaf_entries must be at least ' + str(self.max_push_down))

    def __iter__(self):
        return self._iter_node(self.root)

    def _iter_node(self, node):
        if isinstance(node, dict):
            return iter(sorted(node.items(), key=lambda p: p[0]))
        else:
            keys, children, internal = node

            iterators = map(self._iter_node, children)
            return merge_iters(iter(sorted(internal.items(), key=lambda p: p[0])),
                               itertools.chain(*iterators),
                               key=lambda p: p[0])

    def __contains__(self, x):
        node = self.root
        while True:
            if isinstance(node, dict):
                return x in node

            keys, children, internal = node
            if x in internal:
                return True
            for key, child in zip(keys, children):
                if x <= key:
                    node = child
                    break
            else:
                node = children[-1]


    def __setitem__(self, x, y):
        overflow = self._add_to(self.root, {x: y})
        if overflow is not None:
            keys, children = overflow
            self.root = (keys, children, {})

    # Invariant: len(adds) <= ceiling((max_internal_entries + 1) / max_outdegree)
    # Returns: None (if it fit), or a node one higher level than the input otherwise. Overflowing node has no internal entries.
    def _add_to(self, node, adds):
        if isinstance(node, dict):
            node.update(adds)
            if len(node) <= self.max_leaf_entries:
                return None
            else:
                # We know that:
                #  len(node) <= max_leaf_entries + ceiling((max_internal_entries + 1) / max_outdegree)
                # So if we split the node into 2 we know that either leaf will not be overfull so long as:
                #  max_leaf_entries >= ceiling((max_internal_entries + 1) / max_outdegree)
                # We check this in the constructor. (Actually we could probably relax this if we wanted -- we can split into
                # as many as max_outdegree children here rather than just 2.)
                items = sorted(node.items(), key=lambda p: p[0])
                split_point = len(node)/2
                left, right = items[:split_point], items[split_point:]
                return ([left[-1][0]], [dict(left), dict(right)])

        keys, children, internal = node
        internal.update(adds)

        if len(internal) <= self.max_internal_entries:
            return None

        bucketed_internal = [{k: v for k, v in internal.iteritems() if            k <= keys[0]}] + \
                            [{k: v for k, v in internal.iteritems() if prev_key < k <= key} for prev_key, key in zip(keys, keys[1:])] + \
                            [{k: v for k, v in internal.iteritems() if keys[-1] < k}]
        i, child_adds = max(enumerate(bucketed_internal), key=lambda p: len(p[1]))
        child = children[i]

        # Note that:
        #  len(child_adds) >= ceiling((max_internal_entries + 1) / max_outdegree)
        #
        # i.e. it always contains at least one item. This is important if we hope to make progress!
        # We need to make sure that we don't try to push down too much! Because:
        #  len(adds) <= ceiling((max_internal_entries + 1) / max_outdegree)
        #
        # At this point:
        #  len(internal) <= max_internal_entries + ceiling((max_internal_entries + 1) / max_outdegree)
        # 
        # We ensure that:
        #  len(child_adds) == ceiling((max_internal_entries + 1) / max_outdegree)
        #
        # So after we remove these items from internal, len(internal) <= max_internal_entries again.
        child_adds = dict(child_adds.items()[0:self.max_push_down])

        for k in child_adds:
            del internal[k]

        overflow = self._add_to(child, child_adds)
        if overflow is not None:
            ov_keys, ov_children = overflow
            
            keys[i:i]       = ov_keys     # Keep old key
            children[i:i+1] = ov_children # Replace old child

            n = len(children)
            if n > self.max_outdegree:
                # n > self.max_outdegree
                # n > min_outdegree * 2 - 1
                # n >= min_outdegree * 2
                # n / 2 >= min_outdegree
                split_point = n / 2
                middle = overfull_keys[split_point-1]
                left = (overfull_keys[:split_point-1], overfull_children[:split_point], {k: v for k, v in internal.iteritems() if k <= middle})
                right = (overfull_keys[split_point:], overfull_children[split_point:],  {k: v for k, v in internal.iteritems() if k >  middle})
                return ([middle], [left, right])
        
        return None


t = ABTree(min_outdegree=2, max_leaf_entries=2, max_internal_entries=0)
for x in [3,6,2,1,5,5]:
    print list(t)
    print '.. add', x
    t[x] = str(x)
print list(t)




#class DAM(object):
#   def allocate(self, slots, slot_size_bytes):
#       bytes = slot_size_bytes / slots
#       math.ceil(bytes / page_size_bytes)


