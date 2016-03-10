#kb_to_bytes = 1024
#mb_to_bytes = 1024 * kb_to_bytes
#gb_to_bytes = 1024 * mb_to_bytes

#key_size_bytes = 100
#value_size_bytes = 100
#page_size_bytes = 4 * kb_to_bytes

#memory_bytes = 4 * gb_to_bytes
#num_keys = 1_000_000_000

import math

# Internal nodes a tuple of (keys, list of singleton lists of child nodes)
# Leaf nodes are dictionaries of bounded size
class ABTree(object):
	def __init__(self, min_outdegree):
		if min_outdegree < 2:
			raise ValueError('min_outdegree must be at least 2')

		self.max_outdegree = min_outdegree * 2 - 1
		self.root = [{}]

	def __iter__(self):
		stack = [self.root[0]]
		while stack:
			node = stack.pop()
			if isinstance(node, dict):
				for k, v in node.items():
					yield (k, v)
			else:
				keys, children = node
				if len(keys) == len(children):
					if len(keys) > 1:
						stack.append((keys[1:], children[1:]))
					stack.append(children[0][0])
				else:
					# First time we've seen the node
					stack.append((keys, children[1:]))
					stack.append(children[0][0])

	def __contains__(self, x):
		node = self.root[0]
		while True:
			if isinstance(node, dict):
				return x in node

			keys, children = node
			for key, child in zip(keys, children):
				if x <= key:
					node = child[0]
					break
			else:
				node = children[-1][0]


	def __setitem__(self, x, y):
		overflow = self.add_to(self.root, x, y)
		if overflow is not None:
			self.root = [overflow]

	# Returns: None (if it fit), or a node one higher level than the input otherwise
	def add_to(self, node_ref, x, y):
		node = node_ref[0]
		if isinstance(node, dict):
			node[x] = y
			if len(node) <= self.max_outdegree:
				return None
			else:
				items = sorted(node.items(), key=lambda p: p[0])
				split_point = len(node)/2
				left, right = items[:split_point], items[split_point:]
				return ([left[-1][0]], [[dict(left)], [dict(right)]])

		keys, children = node
		for i, (key, child) in enumerate(zip(keys, children)):
			if key == x:
				return
			elif x < key:
				break
		else:
			i = len(keys)
			child = children[-1]

		overflow = self.add_to(child, x, y)
		if overflow is not None:
			ov_keys, ov_children = overflow
			
			overfull_keys     = keys[:i]     + ov_keys     + keys[i:]
			overfull_children = children[:i] + ov_children + children[i+1:]

			n = len(overfull_children)
			if n <= self.max_outdegree:
				node_ref[0] = (overfull_keys, overfull_children)
			else:
				# n > self.max_outdegree
				# n > min_outdegree * 2 - 1
				# n >= min_outdegree * 2
				# n / 2 >= min_outdegree
				split_point = n / 2
				left = (overfull_keys[:split_point-1], overfull_children[:split_point])
				middle = overfull_keys[split_point-1]
				right = (overfull_keys[split_point:], overfull_children[split_point:])
				return ([middle], [[left], [right]])
		
		return None


t = ABTree(min_outdegree=2)
for x in [3,6,2,1,5,5]:
	print list(t)
	print '.. add', x
	t[x] = str(x)
print list(t)




#class DAM(object):
#	def allocate(self, slots, slot_size_bytes):
#		bytes = slot_size_bytes / slots
#		math.ceil(bytes / page_size_bytes)


