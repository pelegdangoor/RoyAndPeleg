/**
 * Heap
 * <p>
 * An implementation of Fibonacci heap over positive integers
 * with the possibility of not performing lazy melds and
 * the possibility of not performing lazy decrease keys.
 */
public class Heap {
    public final boolean lazyMelds;
    public final boolean lazyDecreaseKeys;
    public HeapItem min = null;

    private int total_cuts = 0;
    private int total_links = 0;
    private int total_heapify_cost = 0;
    private int heap_size = 0;
    private int num_marked_nodes = 0;
    private int num_trees = 0;

    /**
     * Constructor to initialize an empty heap.
     */
    public Heap(boolean lazyMelds, boolean lazyDecreaseKeys) {
        this.lazyMelds = lazyMelds;
        this.lazyDecreaseKeys = lazyDecreaseKeys;
        // student code can be added here
        this.min = null;
        this.heap_size = 0;
        this.num_trees = 0;

        this.total_cuts = 0;
        this.total_links = 0;
        this.total_heapify_cost = 0;
        this.num_marked_nodes = 0;
    }

    // Make node a singleton circular list: next=prev=self
    private static void makeSingleton(HeapNode x) {
        x.next = x;
        x.prev = x;
    }

    // Insert node x into the circular list whose "a" is a member.
    // We insert x right after a.
    private static void spliceAfter(HeapNode a, HeapNode x) {
        HeapNode b = a.next;
        a.next = x;
        x.prev = a;
        x.next = b;
        b.prev = x;
    }

    // Remove node x from its circular list. After removal, x becomes singleton.
    private static void detach(HeapNode x) {
        HeapNode p = x.prev;
        HeapNode n = x.next;
        p.next = n;
        n.prev = p;
        makeSingleton(x);
    }

    // Concatenate two circular lists given representatives a and b.
    // Returns a representative of the merged list (we return a).
    // If one is null -> returns the other.
    private static HeapNode concatLists(HeapNode a, HeapNode b) {
        if (a == null) return b;
        if (b == null) return a;

        HeapNode aNext = a.next;
        HeapNode bPrev = b.prev;

        // connect a <-> b
        a.next = b;
        b.prev = a;

        // connect bPrev <-> aNext
        bPrev.next = aNext;
        aNext.prev = bPrev;

        return a;
    }

    // Update min pointer given a root list representative
    private void recomputeMinFromRoots() {
        if (findMin() == null) {
            min = null;
            return;
        }
        HeapNode start = findMin().node;
        HeapNode cur = start;
        HeapNode best = start;
        do {
            if (cur.item.key < best.item.key) best = cur;
            cur = cur.next;
        } while (cur != start);
        min = best.item;
    }

    // Compare-and-update min using one node (O(1))
    private void considerAsMin(HeapNode x) {
        if (x == null) return;
        if (min == null || x.item.key < min.key) {
            min = x.item;
        }
    }

    /**
     * pre: key > 0
     * <p>
     * Insert (key,info) into the heap and return the newly generated HeapNode.
     */
    public HeapItem insert(int key, String info) {
        return null; // should be replaced by student code
        // needed to use "meld" function
    }

    /**
     * Return the minimal HeapNode, null if empty.
     */
    public HeapItem findMin() {
        return min; // should be replaced by student code
    }

    /**
     * Delete the minimal item.
     */
    public void deleteMin() {
        return; // should be replaced by student code
    }

    /**
     * pre: 0<=diff<=x.key
     * <p>
     * Decrease the key of x by diff and fix the heap.
     */
    public void decreaseKey(HeapItem x, int diff) {
        return; // should be replaced by student code
    }

    /**
     * Delete the x from the heap.
     */
    public void delete(HeapItem x) {
        //need to use decrease_key() and delete_min()
        return; // should be replaced by student code
    }


    /**
     * Meld the heap with heap2
     * pre: heap2.lazyMelds = this.lazyMelds AND heap2.lazyDecreaseKeys = this.lazyDecreaseKeys
     */
    public void meld(Heap heap2) {
        if (heap2 == null || heap2.heap_size == 0) return;
        if (this.heap_size == 0) {
            //take heap2 fields
//            this.anyRoot = heap2.anyRoot;
            this.min = heap2.min;

            this.heap_size = heap2.heap_size;
            this.num_trees = heap2.num_trees;

            this.total_cuts += heap2.total_cuts;
            this.total_links += heap2.total_links;
            this.total_heapify_cost += heap2.total_heapify_cost;
            this.num_marked_nodes += heap2.num_marked_nodes;

            return;
        }

        // 1) concatenate root lists (Fibonacci-style)
        concatLists(this.min.node, heap2.min.node);

        // 2) update min in O(1)
        if (heap2.min != null && (this.min == null || heap2.min.key < this.min.key)) {
            this.min = heap2.min;
        }

        // 3) merge counters/history
        this.heap_size += heap2.heap_size;
        this.num_trees += heap2.num_trees;

        this.total_cuts += heap2.total_cuts;
        this.total_links += heap2.total_links;
        this.total_heapify_cost += heap2.total_heapify_cost;
        this.num_marked_nodes += heap2.num_marked_nodes;

        //todo:
        // 4) If lazyMelds == false => do successive linking after meld
        // We'll implement this after we implement consolidate/link.
        // if (!lazyMelds) { consolidate(); }

    }


    /**
     * Return the number of elements in the heap
     */
    public int size()
    {
        return heap_size;
    }


    /**
     * Return the number of trees in the heap.
     */
    public int numTrees() {
        return num_trees;
    }


    /**
     * Return the number of marked nodes in the heap.
     */
    public int numMarkedNodes() {
        return num_marked_nodes;
    }


    /**
     * Return the total number of links.
     */
    public int totalLinks() {
        return total_links;
    }


    /**
     * Return the total number of cuts.
     */
    public int totalCuts() {
        return total_cuts;
    }


    /**
     * Return the total heapify costs.
     */
    public int totalHeapifyCosts() {
        return total_heapify_cost;
    }


    /**
     * Class implementing a node in a Heap.
     */
    public static class HeapNode {
        public HeapItem item;
        public HeapNode child;
        public HeapNode next;
        public HeapNode prev;
        public HeapNode parent;
        public int rank;
    }

    /**
     * Class implementing an item in a Heap.
     */
    public static class HeapItem {
        public HeapNode node;
        public int key;
        public String info;
    }
}
