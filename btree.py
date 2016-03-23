import math
import random
import itertools
import sys
import bisect
import percache
import pandas as pd
import numpy as np
import collections
from matplotlib import pyplot as plt


kb_to_bytes = 1024
mb_to_bytes = 1024 * kb_to_bytes
gb_to_bytes = 1024 * mb_to_bytes

if False:
    value_dir = 'large-values'
    key_size_bytes = 100
    value_size_bytes = 1000
else:
    value_dir = 'small-values'
    key_size_bytes = 16
    value_size_bytes = 240

page_size_bytes = 4 * kb_to_bytes

#memory_bytes = 4 * mb_to_bytes
memory_bytes = 1 * mb_to_bytes
#memory_bytes = 0

memory_pages = int(math.floor(memory_bytes / page_size_bytes))

cache = percache.Cache(value_dir + "/btree-cache-" + str(memory_bytes), livesync=True)


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


if False:
    from sortedcontainers import SortedDict
else:
    # My own impl seems to be considerably faster than sortedcontainers?!
    class SortedDict(object):
        def __init__(self, *args):
            if len(args) > 0:
                kvs, = args
                self.ks = [k for k, v in kvs]
                self.vs = [v for k, v in kvs]
            else:
                self.ks = []
                self.vs = []

        def __len__(self):
            return len(self.ks)

        def __iter__(self):
            return iter(self.ks)

        def keys(self):
            return self.ks

        def items(self):
            return zip(self.ks, self.vs)

        def iteritems(self):
            return itertools.izip(iter(self.ks), iter(self.vs))

        def update(self, other):
            for k, v in other.iteritems():
                self[k] = v

        def __contains__(self, k):
            return k in self.ks

        def __getitem__(self, k):
            i = bisect.bisect_left(self.ks, k)
            if i < len(self.ks) and self.ks[i] == k:
                return self.vs[i]
            else:
                return None

        def __setitem__(self, k, v):
            i = bisect.bisect_left(self.ks, k)
            if i < len(self.ks) and self.ks[i] == k:
                self.vs[i] = v
            else:
                self.ks[i:i] = [k]
                self.vs[i:i] = [v]

        def __delitem__(self, k):
            i = bisect.bisect_left(self.ks, k)
            if i < len(self.ks) and self.ks[i] == k:
                del self.ks[i]
                del self.vs[i]

        def __str__(self):
            return 'SortedDict({})'.format(self.items())



# Internal nodes a triple of (keys, list of child nodes, dictionary of internal entries)
# Leaf nodes are dictionaries
class InternalNode(object):
    __slots__ = ['keys', 'children', 'internal', 'node_count']
    def __init__(self, keys, children, internal):
        self.keys = keys
        self.children = children
        self.internal = internal
        self.refresh_node_count()

    # Does not include itself in the count
    def refresh_node_count(self):
        self.node_count = sum([1 if isinstance(child, SortedDict) else 1 + child.node_count for child in self.children])

class BEpsilonTree(object):
    def __init__(self, min_outdegree, max_leaf_entries, max_internal_entries):
        self.max_outdegree = min_outdegree * 2 - 1
        self.max_leaf_entries = max_leaf_entries
        self.max_internal_entries = max_internal_entries
        self.root = SortedDict()
        self.stats = {}

        self.max_push_down = int(math.ceil((max_internal_entries + 1) / float(self.max_outdegree)))

        if min_outdegree < 2:
            raise ValueError('min_outdegree must be at least 2')
        if max_internal_entries < 0:
            raise ValueError('max_internal_entries must be at least 0')
        if max_leaf_entries < self.max_push_down:
            raise ValueError('max_leaf_entries must be at least ' + str(self.max_push_down))

    def check(self):
        self._check(self.root, None, None)

    def _check_dict(self, node, mn, mx):
        assert mn is None or ([k for k in node if k <= mn] == []), 'exists %s <= %s' % (node.keys(), mn)
        assert mx is None or ([k for k in node if k >  mx] == []), 'exists %s > %s' % (node.keys(), mx)

    # Returns (number of levels to leaves, number of nodes contained -- including node itself)
    def _check(self, node, mn, mx):
        if isinstance(node, SortedDict):
            assert len(node) <= self.max_leaf_entries
            self._check_dict(node, mn, mx)
            return (0, 1)
        else:
            keys, children, internal, node_count = node.keys, node.children, node.internal, node.node_count
            assert len(keys) + 1 == len(children)
            assert len(children) <= self.max_outdegree
            
            depths, total_count = [], 0
            
            depth, count = self._check(children[0], mn, keys[0])
            depths.append(depth)
            total_count += count
            
            for child_mn, child_mx, child in zip(keys, keys[1:], children[1:]):
                depth, count = self._check(child, child_mn, child_mx)
                depths.append(depth)
                total_count += count
            
            depth, count = self._check(children[-1], keys[-1], mx)
            depths.append(depth)
            total_count += count
            
            depth = depths[0]
            assert len([d for d in depths if d != depth]) == 0

            assert len(internal) <= self.max_internal_entries
            self._check_dict(internal, mn, mx)

            assert node_count == total_count, '{} != {}'.format(node_count, total_count)

            return (depth + 1, total_count + 1)

    def __iter__(self):
        return self._iter_node(self.root)

    def _iter_node(self, node):
        if isinstance(node, SortedDict):
            return node.iteritems()
        else:
            iterators = map(self._iter_node, node.children)
            return merge_iters(node.internal.iteritems(),
                               itertools.chain(*iterators),
                               key=lambda p: p[0])

    def __contains__(self, x):
        level = 0
        node = self.root
        remaining_memory_pages = memory_pages
        while True:
            self.stats.setdefault('reads', collections.Counter())[level] += 1

            remaining_memory_pages, is_cached = self.test_is_cached(remaining_memory_pages, node)
            if not is_cached:
                self.stats.setdefault('uncached_reads', collections.Counter())[level] += 1

            if isinstance(node, SortedDict):
                return x in node

            if x in node.internal:
                return True
            
            node = node.children[bisect.bisect(node.keys, x)]
            level = level + 1

    def __setitem__(self, x, y):
        overflow = self._add_to(0, self.root, {x: y})
        if overflow is not None:
            keys, children = overflow
            self.root = InternalNode(keys, children, SortedDict())

    # Invariant: len(adds) <= ceiling((max_internal_entries + 1) / max_outdegree)
    # Returns: None (if it fit), or a node one higher level than the input otherwise. Overflowing node has no internal entries.
    def _add_to(self, level, node, adds):
        self.stats.setdefault('writes', collections.Counter())[level] += 1

        if isinstance(node, SortedDict):
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
                items = node.items()
                split_point = len(items)/2
                left, right = items[:split_point], items[split_point:]
                return ([left[-1][0]], [SortedDict(left), SortedDict(right)])

        keys, children, internal = node.keys, node.children, node.internal
        internal.update(adds)

        if len(internal) <= self.max_internal_entries:
            return None

        biggest_bucket_ix = 0
        bucketed_internal = [{} for _ in children]
        for k, v in internal.iteritems():
            # j is such that all k' in keys[:j] have k' < k, and all k' in keys[j:] have k' >= k
            j = bisect.bisect_left(keys, k)
            bucket = bucketed_internal[j]
            bucket[k] = v
            if len(bucket) > len(bucketed_internal[biggest_bucket_ix]):
                biggest_bucket_ix = j

        child_adds = bucketed_internal[biggest_bucket_ix]
        child      = children[biggest_bucket_ix]

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
        if len(child_adds) > self.max_push_down:
            child_adds = dict(child_adds.items()[0:self.max_push_down])

        for k in child_adds:
            del internal[k]

        overflow = self._add_to(level + 1, child, child_adds)
        if overflow is not None:
            ov_keys, ov_children = overflow
            
            keys[biggest_bucket_ix:biggest_bucket_ix]       = ov_keys     # Keep old key
            children[biggest_bucket_ix:biggest_bucket_ix+1] = ov_children # Replace old child
            
            n = len(children)
            if n > self.max_outdegree:
                # n > self.max_outdegree
                # n > min_outdegree * 2 - 1
                # n >= min_outdegree * 2
                # n / 2 >= min_outdegree
                split_point = n / 2
                middle = keys[split_point-1]

                internal_left, internal_right = [], []
                for k, v in internal.iteritems():
                    if k <= middle:
                        internal_left.append((k, v))
                    else:
                        internal_right.append((k, v))

                left = InternalNode(keys[:split_point-1], children[:split_point], SortedDict(internal_left))
                right = InternalNode(keys[split_point:], children[split_point:],  SortedDict(internal_right))
                return ([middle], [left, right])
        
        node.refresh_node_count() # We or a child might have mutated children
        return None

    def __str__(self):
        lines = []
        self._show_node(self.root, 0, lines)
        return '\n'.join(lines)

    def _show_node(self, node, level, lines):
        if isinstance(node, SortedDict):
            if len(node) == 0:
                lines.append('%s0 items?!?' % (level * '\t',))
            else:
                lines.append('%s%d items between %s and %s' % (level * '\t', len(node), node.keys()[0], node.keys()[-1]))
        else:
            keys, children, internal = node.keys, node.children, node.internal

            if len(internal) > 0:
                lines.append('%s%d items between %s and %s' % (level * '\t', len(internal), internal.keys()[0], internal.keys()[-1]))
            
            lines.append('%sitems <= %s' % (level * '\t', keys[0]))
            self._show_node(children[0], level + 1, lines)
            
            for prev_key, key, child in zip(keys, keys[1:], children[1:]):
                lines.append('%s%s < items <= %s' % (level * '\t', prev_key, key))
                self._show_node(child, level + 1, lines)

            lines.append('%s%s < items' %(level * '\t', keys[-1]))
            self._show_node(children[-1], level + 1, lines)



@cache
def experiment(*args):
    return experiment_uncached(*args)

def experiment_uncached(tree, num_keys):
    if tree == 'btree':
        max_internal_entries = 0
        max_outdegree = 1 + int(math.floor(page_size_bytes / float(key_size_bytes)))
    elif tree == 'brt':
        max_internal_entries = int(math.floor((page_size_bytes - 2 * key_size_bytes) / float(key_size_bytes + value_size_bytes)))
        max_outdegree = 3
    elif tree == 'fractal':
        # Wrong way around:
        #max_internal_entries = int(math.ceil(math.sqrt(page_size_bytes / float(key_size_bytes + value_size_bytes))))
        #max_outdegree = 1 + int(math.floor((page_size_bytes - (max_internal_entries * (key_size_bytes + value_size_bytes))) / float(key_size_bytes)))
        # Correctly setting fanout to sqrt(B):
        max_outdegree = 1 + int(math.floor(math.sqrt(page_size_bytes / float(key_size_bytes))))
        max_internal_entries = int(math.floor((page_size_bytes - (max_outdegree - 1) * key_size_bytes) / float(key_size_bytes + value_size_bytes)))
    else:
        raise ValueError('Bad tree type ' + tree)

    min_outdegree = int(math.floor((max_outdegree + 1) / 2))
    max_leaf_entries = int(math.floor(page_size_bytes / float(key_size_bytes + value_size_bytes)))
    t = BEpsilonTree(min_outdegree, max_leaf_entries, max_internal_entries)

    assert max_internal_entries * (key_size_bytes + value_size_bytes) + \
           (max_outdegree - 1) * key_size_bytes \
           <= page_size_bytes
    assert max_leaf_entries * (key_size_bytes + value_size_bytes) \
           <= page_size_bytes

    # Tree of height h has
    #   max_outdegree^(h - 1) nodes in the last level
    #   max_outdegree^h - 1 nodes overall
    required_leaf_pages = math.ceil(num_keys / float(max_leaf_entries))
    estimated_levels = 1 + math.log(required_leaf_pages, max_outdegree) # Assumes all items reach the leaves: not necessarily true

    max_memory_levels = math.log(memory_pages + 1, max_outdegree)
    #print memory_pages, max_outdegree, math.log(memory_pages + 1, max_outdegree)
    
    params = {
        'max_internal_entries': max_internal_entries,
        'min_outdegree': min_outdegree,
        'max_outdegree': max_outdegree,
        'max_leaf_entries': max_leaf_entries,
        'max_memory_levels': max_memory_levels,
        'estimated_levels': estimated_levels,
    }
    print params

    test = [random.randrange(0, 1000 * num_keys) for _ in range(0, num_keys)]
    
    for x in test:
        t[x] = ()
    
    for x in test:
        x in t
    
    t.check()
    #print t

    # If memory_levels = 1 then the root page *plus all its children* fits in memory
    #   first_uncached_level = 1
    #   fractional_uncached_amount = 0
    #   total = stats[1] * 0 + sum(stats[2:])
    #   
    # if memory_levels = 1.01
    #   first_uncached_level = 2
    #   fractional_uncached_amount = 0.99
    #   totaly = stats[2] * 0.99 + sum(stats[3:])
    #
    # This is fine but there is an off-by-one: we should only be counting levels >= 2, not 1
    first_uncached_level = int(math.ceil(max_memory_levels))
    def summarise(stats):
        levels = max(stats) + 1 # If max level key is 1, we had 2 items in the map
        fractional_uncached_amount = min(first_uncached_level - max_memory_levels, levels - max_memory_levels)
        
        total = stats.get(first_uncached_level, 0) * fractional_uncached_amount
        for level, amount in stats.items():
            if level > first_uncached_level:
                total += amount

        return total
    
    return {
        'params': params,
        'uncached_reads': summarise(t.stats['reads']),
        'uncached_writes': summarise(t.stats['writes'])
    }

if True:
    experiment_uncached('btree',   300)
    experiment_uncached('fractal', 300)
elif False:
    tree, = sys.argv[1:]

    rows = {}
    for num_keys in [x * int(math.pow(10, e)) for e in range(6) for x in (1, 3, 7)]:
        res = experiment(tree, num_keys)
        rows[num_keys] = res
        
    df = pd.DataFrame.from_dict(rows)
    df.T.plot(logx=True, logy=True)

    plt.show()
elif True:
    stat, = sys.argv[1:] # e.g. 'uncached_reads'

    num_keyss = [x * int(math.pow(10, e)) for e in range(6) for x in (1, 3, 7)]

    rows = {}
    for tree in ('btree', 'brt', 'fractal'):
        row = rows[tree] = {}
        for num_keys in num_keyss:
            res = experiment(tree, num_keys)
            row[num_keys] = res[stat]

    df = pd.DataFrame.from_dict(rows)
    ax = df.plot(logx=True, logy=True)

    memory_to_data = [
        min(1.0, memory_bytes
                    / float(num_keys * (key_size_bytes + value_size_bytes))) \
        for num_keys in num_keyss]

    pd.DataFrame.from_dict({
        'num_keys': num_keyss,
        'memory_to_data': memory_to_data,
    }).set_index('num_keys').plot(secondary_y=True, logx=True, logy=False, ax=ax)

    plt.show()
else:
    if False:
        t = BEpsilonTree(min_outdegree=2, max_leaf_entries=2, max_internal_entries=0)
    else:
        min_outdegree = random.randrange(2, 10)
        max_outdegree = min_outdegree * 2 - 1
        max_internal_entries = random.randrange(0, 10)
        
        max_push_down = int(math.ceil((max_internal_entries + 1) / float(max_outdegree)))
        max_leaf_entries = random.randrange(max_push_down, max_push_down + 10)

        print (min_outdegree, max_leaf_entries, max_internal_entries)

        t = BEpsilonTree(min_outdegree, max_leaf_entries, max_internal_entries)

    if False:
        test = [3,6,2,1,5,5]
    else:
        test = [random.randrange(0, 100) for _ in range(0, 1000)]

    if True:
        for x in test:
            print t
            t.check()
            print '.. add', x
            t[x] = str(x)
        print t
        t.check()
    else:
        for x in test:
            t.check()
            t[x] = str(x)
        t.check()

    for x in test:
        x in t

    assert {k for k, _ in t} == set(test)
    print t.stats
