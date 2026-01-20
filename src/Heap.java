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
    /**
     * deleteMin:
     * Lecture style:
     * 1) remove the min root z from the root list
     * 2) move all children of z to the root list (unmark + set parent=null)
     * 3) successiveLinking() (consolidate)
     */
    public void deleteMin() {
        if (this.min == null) return;

        HeapNode z = this.min.node;

        // special case: heap has exactly one node
        if (this.size == 1) {
            makeEmptyStructure();
            return;
        }

        removeMinRoot(z);
        addMinChildrenToRootList(z);

        // after removing min and exposing its children:
        // must consolidate (successive linking)
        successiveLinking();

        // optional debug hooks if you added them:
        // debugMinIsRoot("after deleteMin");
        // debugCheckCircular(this.firstRoot, "root list after deleteMin", this.size + 10);
        // debugCheckNumTrees("after deleteMin");
    }
    /**
     * Step 1 of deleteMin: remove the min root z from the root list.
     */
    private void removeMinRoot(HeapNode z) {
        // remove z from root list (O(1))
        removeRoot(z);

        this.size -= 1;
        this.numTrees -= 1;

        // disconnect z completely (not required, but cleaner)
        z.next = z;
        z.prev = z;
    }
    /**
     * Step 2 of deleteMin: add all children of z to the root list.
     * This is NOT counted as cuts.
     */
    private void addMinChildrenToRootList(HeapNode z) {
        if (z.child == null) {
            // no children to add
            return;
        }

        HeapNode childList = z.child;
        int k = z.rank;     // number of children (how many trees we will add)

        // detach children list from z
        z.child = null;
        z.rank = 0;

        // for each child:
        // parent <- null
        // mark <- 0
        HeapNode c = childList;
        do {
            c.parent = null;

            if (c.marked) {
                c.marked = false;
                this.numMarked--;
            }

            c = c.next;
        } while (c != childList);

        // splice the entire child circular list into the root circular list
        spliceRootList(childList);

        // each child becomes a root => number of trees increases by k
        this.numTrees += k;
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

    /**
     * Clear only the CURRENT heap structure (make it empty),
     * but DO NOT reset historical counters:
     * totalLinks, totalCuts, totalHeapifyCosts.
     */
    private void makeEmptyStructure() {
        this.min = null;
        this.firstRoot = null;
        this.size = 0;
        this.numTrees = 0;
        this.numMarked = 0;
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
    /**
     * Consolidating / Successive Linking
     * Exactly follows the lecture pseudo-code:
     * consolidate(x) = toBuckets(x) + fromBuckets()
     */
    private void successiveLinking() {
        if (this.firstRoot == null) {
            this.min = null;
            this.numTrees = 0;
            return;
        }

        // Step 1: allocate buckets B[0..log n]
        int maxRank = upperBoundRank(this.size);
        HeapNode[] B = new HeapNode[maxRank + 1];

        // Step 2: to-buckets(firstRoot)
        toBuckets(B);

        // Step 3: from-buckets()
        HeapNode minRoot = fromBuckets(B);

        // Update heap pointers/statistics
        this.firstRoot = minRoot;           // convenient: firstRoot = minRoot
        this.min = (minRoot == null ? null : minRoot.item);
    }

    /**
     * to-buckets(x) from the slide:
     *
     * for i=0..log_phi(n): B[i]=null
     * x.prev.next = null   (break the circular root list)
     * while x != null:
     *     y = x
     *     x = x.next
     *     while B[y.rank] != null:
     *         y = link(y, B[y.rank])
     *         B[y.rank-1] = null
     *     B[y.rank] = y
     */
    private void toBuckets(HeapNode[] B) {
        // break circular root list -> turn it into a linear list
        HeapNode head = breakRootCircularToLinear();
        HeapNode x = head;

        // we will rebuild numTrees later in fromBuckets(), so reset now
        this.numTrees = 0;

        while (x != null) {
            HeapNode y = x;
            x = x.next;      // advance in linear list

            // isolate y as singleton root (important before linking)
            y.next = y;
            y.prev = y;
            y.parent = null;

            int d = y.rank;
            while (B[d] != null) {
                HeapNode other = B[d];
                B[d] = null;

                // link y with other (same rank) => new root returned
                y = link(y, other);
                this.totalLinks++;

                d = y.rank;
            }
            B[d] = y;
        }
    }

    /**
     * from-buckets() from the slide:
     *
     * x = null
     * for i=0..log_phi(n):
     *     if B[i] != null:
     *         if x == null:
     *             x = B[i]
     *             x.next = x
     *             x.prev = x
     *         else:
     *             insert-after(x, B[i])
     *             if B[i].key < x.key: x = B[i]
     * return x
     */
    private HeapNode fromBuckets(HeapNode[] B) {
        HeapNode x = null; // will become the minimum root
        this.numTrees = 0;

        for (int i = 0; i < B.length; i++) {
            HeapNode r = B[i];
            if (r == null) continue;

            // ensure r is a clean root singleton
            r.parent = null;
            if (r.marked) {
                r.marked = false;
                this.numMarked--;
            }
            r.next = r;
            r.prev = r;

            if (x == null) {
                x = r;
            } else {
                insertAfter(x, r); // O(1) splice into circular list
                if (r.item.key < x.item.key) {
                    x = r;
                }
            }
            this.numTrees++;
        }

        return x;
    }

    /** O(1): insert singleton node 'b' after node 'a' in a circular doubly list */
    private void insertAfter(HeapNode a, HeapNode b) {
        // a ... a.next
        b.next = a.next;
        b.prev = a;
        a.next.prev = b;
        a.next = b;
    }

    /**
     * Break the circular root list into a linear list and return the head.
     * This matches the slide line: x.prev.next = null
     */
    private HeapNode breakRootCircularToLinear() {
        HeapNode head = this.firstRoot;
        if (head == null) return null;

        HeapNode tail = head.prev;

        // break circle: tail.next = null
        tail.next = null;

        // optional cleanup: head.prev = null (not required but clearer)
        head.prev = null;

        return head;
    }

    /** upper bound on possible rank: O(log n) */
    private int upperBoundRank(int n) {
        int r = 0;
        int x = 1;
        while (x <= n && r < 50) {
            x <<= 1;
            r++;
        }
        return r + 2;
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


    /**
     * cut(x,y) from the slide:
     * Cut node x from its parent y and move x to the root list.
     */
    private void cut(HeapNode x, HeapNode y) {
        // 1) detach x from y's child list
        if (x.next == x) {
            // x was the only child
            y.child = null;
        } else {
            // remove x from circular sibling list
            x.prev.next = x.next;
            x.next.prev = x.prev;

            // if y.child was pointing to x, move it forward
            if (y.child == x) {
                y.child = x.next;
            }
        }

        // 2) update y
        y.rank--;

        // 3) make x a root
        x.parent = null;

        // x.mark <- 0
        if (x.marked) {
            x.marked = false;
            this.numMarked--;
        }

        // isolate x as singleton circular list
        x.next = x;
        x.prev = x;

        // 4) add x to root list
        if (this.firstRoot == null) {
            this.firstRoot = x;
        } else {
            insertAfter(this.firstRoot, x);
        }
        this.numTrees++;

        // update min if needed (now x is definitely a root)
        if (this.min == null || x.item.key < this.min.key) {
            this.min = x.item;
        }
    }

    /**
     * cascading-cut(x,y) from the slide:
     * cut(x,y)
     * if y.parent != null:
     *    if y.mark == 0 -> y.mark=1
     *    else cascading-cut(y, y.parent)
     */
    private void cascadingCut(HeapNode x) {
        HeapNode y = x.parent;
        if (y == null) return;

        // cut(x,y)
        cut(x, y);
        this.totalCuts++;

        // if y.parent != null then ...
        HeapNode z = y.parent;
        if (z != null) {
            if (!y.marked) {
                y.marked = true;
                this.numMarked++;
            } else {
                cascadingCut(y);
            }
        }

        // requirement: if melds are non-lazy, consolidate after each cut insertion
        if (!this.lazyMelds) {
            successiveLinking();
        }
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
