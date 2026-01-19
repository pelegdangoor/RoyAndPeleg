/**
 * Heap
 *
 * An implementation of Fibonacci heap over (non-negative) integers
 * with two optional behaviors:
 *  - lazyMelds:
 *      true  -> like Fibonacci heap: meld is O(1) (just concatenate root lists)
 *      false -> after meld, perform successive linking (consolidation)
 *  - lazyDecreaseKeys:
 *      true  -> like Fibonacci heap: decreaseKey uses (cascading) cuts
 *      false -> like (lazy) binomial heaps: decreaseKey uses heapifyUp (swapping items)
 *
 * Notes:
 *  - Keys are stored in HeapItem (not in HeapNode).
 *  - We keep back pointers HeapItem.node consistent under swaps.
 *  - We do NOT use any Java collection library data structures.
 */
public class Heap {

    public final boolean lazyMelds;
    public final boolean lazyDecreaseKeys;

    /** Pointer to the minimal item in the heap (null if empty). */
    public HeapItem min;

    /* =====================
     * Internal heap fields
     * ===================== */

    /** A pointer to an arbitrary root in the circular root list (null if empty). */
    private HeapNode firstRoot;

    /** Number of items in the heap. */
    private int size;

    /** Number of trees (roots) in the heap. */
    private int numTrees;

    /** Number of marked nodes (only possible when lazyDecreaseKeys==true). */
    private int numMarked;

    /** Total links performed since creation. */
    private int totalLinks;

    /** Total cuts performed since creation (does NOT include cuts done inside deleteMin). */
    private int totalCuts;

    /** Total heapifyUp swap cost accumulated since creation (only when lazyDecreaseKeys==false). */
    private int totalHeapifyCosts;


    /**
     * Constructor to initialize an empty heap.
     * Runs in O(1).
     */
    public Heap(boolean lazyMelds, boolean lazyDecreaseKeys) {
        this.lazyMelds = lazyMelds;
        this.lazyDecreaseKeys = lazyDecreaseKeys;
        this.min = null;
        this.firstRoot = null;
        this.size = 0;
        this.numTrees = 0;
        this.numMarked = 0;
        this.totalLinks = 0;
        this.totalCuts = 0;
        this.totalHeapifyCosts = 0;
    }


    /**
     * pre: key > 0
     *
     * Insert (key,info) into the heap and return the newly generated HeapItem.
     *
     * Implementation requirement (as in the PDF): insert is done via meld.
     *
     * Worst-case time:
     *  - lazyMelds=true  : O(1)
     *  - lazyMelds=false : O(log n) due to consolidation in meld
     */
    public HeapItem insert(int key, String info) {
        HeapItem item = new HeapItem();
        item.key = key;
        item.info = info;

        HeapNode node = new HeapNode();
        node.item = item;
        item.node = node;

        node.child = null;
        node.parent = null;
        node.rank = 0;
        node.marked = false;
        node.next = node;
        node.prev = node;

        // Build a singleton heap and meld it in (per assignment).
        Heap singleton = new Heap(this.lazyMelds, this.lazyDecreaseKeys);
        singleton.firstRoot = node;
        singleton.min = item;
        singleton.size = 1;
        singleton.numTrees = 1;

        this.meld(singleton);
        return item;
    }


    /**
     * Return the minimal item, or null if empty.
     * Runs in O(1).
     */
    public HeapItem findMin() {
        return this.min;
    }


    /**
     * Delete the minimal item.
     *
     * Worst-case time: O(n) (because successive linking can be linear in worst case).
     * Amortized time (Fibonacci / lazy binomial style): O(log n).
     */
    public void deleteMin() {
        if (this.min == null) {
            return;
        }

        HeapNode z = this.min.node;
        int zRank = z.rank;

        // If this was the only node in the heap.
        if (this.size == 1) {
            this.min = null;
            this.firstRoot = null;
            this.size = 0;
            this.numTrees = 0;
            this.numMarked = 0; // should already be 0
            return;
        }

        // Remove z from the root list.
        removeRoot(z);
        this.size -= 1;
        this.numTrees -= 1; // removing z tree

        // Add z's children to the root list (WITHOUT increasing totalCuts!).
        if (z.child != null) {
            // Detach child list from z.
            HeapNode childList = z.child;
            z.child = null;
            z.rank = 0;

            // Unparent all children and unmark them.
            HeapNode c = childList;
            do {
                c.parent = null;
                if (c.marked) {
                    c.marked = false;
                    this.numMarked -= 1;
                }
                c = c.next;
            } while (c != childList);

            // Splice child roots into the root list.
            spliceRootList(childList);
            this.numTrees += zRank; // each child becomes a new tree
        }

        // Consolidate (successive linking) is ALWAYS required after deleteMin.
        successiveLinking();
    }


    /**
     * pre: 0<=diff<=x.key
     *
     * Decrease the key of x by diff and fix the heap.
     *
     * Worst-case time:
     *  - lazyDecreaseKeys=true  : O(n) (cascading cuts may cut many nodes)
     *  - lazyDecreaseKeys=false : O(log n) (heapifyUp may bubble to root)
     */
    public void decreaseKey(HeapItem x, int diff) {
        if (x == null || x.node == null) return;

        x.key -= diff;
        HeapNode v = x.node;
        HeapNode p = v.parent;

        // אם אין הפרה מול אבא → לא עושים כלום מעבר,
        // אבל גם לא נעדכן min אם v לא שורש!
        if (p == null || x.key >= p.item.key) {
            if (v.parent == null && (this.min == null || x.key <= this.min.key)) {
                this.min = x;
            }
            return;
        }

        if (this.lazyDecreaseKeys) {
            cascadingCut(v); // אחרי זה v הופך לשורש
            if (v.parent == null && x.key <= this.min.key) {
                this.min = x;
            }
        } else {
            int swaps = heapifyUp(v);
            this.totalHeapifyCosts += swaps;

            // x אולי טיפס (HeapItem נשאר אותו אובייקט), נעדכן min רק אם הוא הגיע לשורש
            if (x.node.parent == null && x.key <= this.min.key) {
                this.min = x;
            }
        }
    }



    /**
     * Delete x from the heap.
     *
     * Required by assignment: delete implemented via decreaseKey + deleteMin.
     * We force x to become the chosen minimum even if there are duplicate keys,
     * by setting min to x when its key ties the minimum.
     */
    public void delete(HeapItem x) {
        if (x == null || x.node == null || this.min == null) return;

        if (x == this.min) {
            deleteMin();
            return;
        }

        // מורידים אותו למפתח 0
        decreaseKey(x, x.key);

        // אם עדיין לא שורש – נכפה שהוא יהפוך לשורש כדי ש-min יוכל להיות הוא
        if (x.node != null && x.node.parent != null) {
            if (this.lazyDecreaseKeys) {
                // Cut "forced": נבצע cascadingCut גם אם אין הפרה
                cascadingCut(x.node);
            } else {
                // במקרה heapifyUp, נכפה טיפוס גם במקרי שוויון (<=)
                int extra = heapifyUpForceEqual(x.node);
                this.totalHeapifyCosts += extra;
            }
        }

        // עכשיו הוא שורש ולכן אפשר לכוון אליו min בלי לשבור אינווריאנטים
        if (x.node != null && x.node.parent == null) {
            this.min = x;
        }

        deleteMin();
    }



    /**
     * Meld the heap with heap2.
     * pre: heap2.lazyMelds == this.lazyMelds AND heap2.lazyDecreaseKeys == this.lazyDecreaseKeys
     *
     * Worst-case time:
     *  - lazyMelds=true  : O(1)
     *  - lazyMelds=false : O(n) worst-case due to successiveLinking
     */
    public void meld(Heap heap2) {
        if (heap2 == null || heap2.min == null) {
            return;
        }
        if (this.min == null) {
            // Adopt heap2 completely.
            this.firstRoot = heap2.firstRoot;
            this.min = heap2.min;
            this.size = heap2.size;
            this.numTrees = heap2.numTrees;
            this.numMarked = heap2.numMarked;
            this.totalLinks = heap2.totalLinks;
            this.totalCuts = heap2.totalCuts;
            this.totalHeapifyCosts = heap2.totalHeapifyCosts;

            // Make heap2 unusable.
            heap2.clear();
            return;
        }

        // Merge histories (as required by PDF).
        this.totalLinks += heap2.totalLinks;
        this.totalCuts += heap2.totalCuts;
        this.totalHeapifyCosts += heap2.totalHeapifyCosts;

        // Merge sizes/statistics.
        this.size += heap2.size;
        this.numTrees += heap2.numTrees;
        this.numMarked += heap2.numMarked;

        // Concatenate root lists in O(1).
        this.firstRoot = concatenateCircularLists(this.firstRoot, heap2.firstRoot);

        // Update min.
        if (heap2.min.key <= this.min.key) {
            this.min = heap2.min;
        }

        // Make heap2 unusable.
        heap2.clear();

        // If meld is non-lazy, consolidate immediately.
        if (!this.lazyMelds) {
            successiveLinking();
        }
    }


    /** Return the number of elements in the heap. Runs in O(1). */
    public int size() {
        return this.size;
    }


    /** Return the number of trees in the heap. Runs in O(1). */
    public int numTrees() {
        return this.numTrees;
    }


    /** Return the number of marked nodes in the heap. Runs in O(1). */
    public int numMarkedNodes() {
        return this.numMarked;
    }


    /** Return the total number of links. Runs in O(1). */
    public int totalLinks() {
        return this.totalLinks;
    }


    /** Return the total number of cuts. Runs in O(1). */
    public int totalCuts() {
        return this.totalCuts;
    }


    /** Return the total heapify costs. Runs in O(1). */
    public int totalHeapifyCosts() {
        return this.totalHeapifyCosts;
    }


    /* ==================================================
     *                  Helper methods
     * ================================================== */

    /** Clear this heap's pointers and counters (used to make heap2 unusable after meld). */
    private void clear() {
        this.min = null;
        this.firstRoot = null;
        this.size = 0;
        this.numTrees = 0;
        this.numMarked = 0;
        this.totalLinks = 0;
        this.totalCuts = 0;
        this.totalHeapifyCosts = 0;
    }


    /** Remove a root node from the root list and update firstRoot if needed. Runs in O(1). */
    private void removeRoot(HeapNode x) {
        if (x == null) {
            return;
        }
        if (x.next == x) {
            // List becomes empty.
            this.firstRoot = null;
        } else {
            x.prev.next = x.next;
            x.next.prev = x.prev;
            if (this.firstRoot == x) {
                this.firstRoot = x.next;
            }
        }
        x.next = x;
        x.prev = x;
    }


    /** Splice an existing circular list of roots into this heap's root list in O(1). */
    private void spliceRootList(HeapNode otherFirst) {
        if (otherFirst == null) {
            return;
        }
        if (this.firstRoot == null) {
            this.firstRoot = otherFirst;
            return;
        }
        this.firstRoot = concatenateCircularLists(this.firstRoot, otherFirst);
    }


    /** Concatenate two circular doubly-linked lists and return the resulting first pointer. */
    private static HeapNode concatenateCircularLists(HeapNode a, HeapNode b) {
        if (a == null) {
            return b;
        }
        if (b == null) {
            return a;
        }

        HeapNode aNext = a.next;
        HeapNode bPrev = b.prev;

        a.next = b;
        b.prev = a;

        bPrev.next = aNext;
        aNext.prev = bPrev;

        return a;
    }


    /**
     * Successive linking / consolidation.
     * Rebuilds the root list so there is at most one tree of each rank.
     *
     * Worst-case time: O(numTrees + #links) = O(n) worst-case.
     */
    private void successiveLinking() {
        if (this.firstRoot == null) {
            this.min = null;
            this.numTrees = 0;
            return;
        }

        // Upper bound on rank: O(log n). We use log2(n)+2 as a safe bound.
        int maxRank = 1;
        int n = this.size;
        while ((1 << maxRank) <= n && maxRank < 30) {
            maxRank++;
        }
        maxRank += 2;

        HeapNode[] buckets = new HeapNode[maxRank + 1];

        // Iterate over the current roots and detach each root into singleton.
        HeapNode start = this.firstRoot;
        HeapNode w = start;
        do {
            HeapNode next = w.next;
            w.next = w;
            w.prev = w;

            int d = w.rank;
            while (buckets[d] != null) {
                HeapNode y = buckets[d];
                buckets[d] = null;
                w = link(w, y);
                this.totalLinks += 1;
                d = w.rank;
            }
            buckets[d] = w;

            w = next;
        } while (w != start);

        // Rebuild root list from buckets.
        this.firstRoot = null;
        this.min = null;
        this.numTrees = 0;

        for (int i = 0; i < buckets.length; i++) {
            HeapNode x = buckets[i];
            if (x == null) {
                continue;
            }
            // Make sure x is a singleton root list.
            x.parent = null;
            x.next = x;
            x.prev = x;

            if (this.firstRoot == null) {
                this.firstRoot = x;
            } else {
                this.firstRoot = concatenateCircularLists(this.firstRoot, x);
            }

            this.numTrees += 1;
            if (this.min == null || x.item.key <= this.min.key) {
                this.min = x.item;
            }
        }
    }


    /**
     * Link two roots of the same rank and return the new root.
     * Assumes x and y are both singleton roots (not inside a larger root list).
     */
    private HeapNode link(HeapNode x, HeapNode y) {
        if (y.item.key < x.item.key) {
            HeapNode tmp = x;
            x = y;
            y = tmp;
        }

        // y becomes a child of x.
        y.parent = x;

        // In Fibonacci-heap style, a node that becomes a child is unmarked.
        if (y.marked) {
            y.marked = false;
            this.numMarked -= 1;
        }

        // Insert y into x's child list.
        if (x.child == null) {
            x.child = y;
            y.next = y;
            y.prev = y;
        } else {
            HeapNode c = x.child;
            // Insert y right after c.
            y.next = c.next;
            y.prev = c;
            c.next.prev = y;
            c.next = y;
        }

        x.rank += 1;
        return x;
    }


    /**
     * HeapifyUp by swapping HeapItems with parents until heap order holds.
     * Returns the number of swaps performed (the cost). Worst-case O(log n).
     */
    private int heapifyUp(HeapNode v) {
        int swaps = 0;
        while (v.parent != null && v.item.key < v.parent.item.key) {
            swapItems(v, v.parent);
            swaps++;
            v = v.parent;
        }
        return swaps;
    }

    private int heapifyUpForceEqual(HeapNode v) {
        int swaps = 0;
        while (v.parent != null && v.item.key <= v.parent.item.key) {
            swapItems(v, v.parent);
            swaps++;
            v = v.parent;
        }
        return swaps;
    }



    /** Swap the HeapItem objects stored in two nodes and keep back pointers consistent. */
    private static void swapItems(HeapNode a, HeapNode b) {
        HeapItem tmp = a.item;
        a.item = b.item;
        b.item = tmp;

        // keep back pointers consistent
        a.item.node = a;
        b.item.node = b;
    }


    /** Perform a cascading cut starting from node x (which violates heap order w.r.t its parent). */
    private void cascadingCut(HeapNode x) {
        HeapNode p = x.parent;
        if (p == null) {
            return;
        }

        cut(x);              // cut x from p and make it a root
        this.totalCuts += 1; // counted (unlike deleteMin's child detach)

        // After cut, x is a root.
        if (x.item.key <= this.min.key) {
            this.min = x.item;
        }

        // Cascading logic.
        if (p.parent != null) {
            if (!p.marked) {
                p.marked = true;
                this.numMarked += 1;
            } else {
                cascadingCut(p);
            }
        }

        // Requirement: in non-lazy meld mode, every such "meld" (adding a cut tree)
        // should trigger successive linking.
        if (!this.lazyMelds) {
            successiveLinking();
        }
    }


    /**
     * Cut node x from its parent and add it to the root list.
     * Runs in O(1).
     */
    private void cut(HeapNode x) {
        HeapNode p = x.parent;
        if (p == null) {
            return;
        }

        // Remove x from p's child list.
        if (x.next == x) {
            // x was the only child
            p.child = null;
        } else {
            x.prev.next = x.next;
            x.next.prev = x.prev;
            if (p.child == x) {
                p.child = x.next;
            }
        }
        p.rank -= 1;

        // x becomes a root
        x.parent = null;

        // Unmark x when it becomes a root.
        if (x.marked) {
            x.marked = false;
            this.numMarked -= 1;
        }

        // Make x a singleton circular list.
        x.next = x;
        x.prev = x;

        // Add x to the root list.
        if (this.firstRoot == null) {
            this.firstRoot = x;
        } else {
            this.firstRoot = concatenateCircularLists(this.firstRoot, x);
        }
        this.numTrees += 1;
    }


    /* ==================================================
     *             Classes required by the skeleton
     * ================================================== */

    /**
     * Class implementing a node in a Heap.
     *
     * IMPORTANT: We did not change any existing fields from the skeleton.
     * We added only the 'marked' field.
     */
    public static class HeapNode {
        public HeapItem item;
        public HeapNode child;
        public HeapNode next;
        public HeapNode prev;
        public HeapNode parent;
        public int rank;

        // Added field (allowed by the assignment):
        public boolean marked;
    }

    /** Class implementing an item in a Heap. */
    public static class HeapItem {
        public HeapNode node;
        public int key;
        public String info;
    }
}
