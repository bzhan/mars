# Unit test for topological sort

import unittest

from ss2hcsp.util.topsort import topological_sort, TopologicalSortException

class TopSortTest(unittest.TestCase):
    def testTopSort1(self):
        data = {
            1: {2, 3},
            2: {3, 4},
            3: {4},
            4: {}
        }
        self.assertEqual(topological_sort(data), [4, 3, 2, 1])

    def testTopSort2(self):
        data = {
            1: {2, 3},
            2: {3, 4},
            3: {4},
            4: {1}
        }
        self.assertRaises(TopologicalSortException, topological_sort, data)

    def testTopSort3(self):
        data = {
            1: {4},
            2: {4},
            3: {4},
            4: {}
        }
        self.assertEqual(topological_sort(data), [4, 1, 2, 3])


if __name__ == "__main__":
    unittest.main()
