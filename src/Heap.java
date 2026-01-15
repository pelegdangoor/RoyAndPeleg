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
    private static void makeCircular(HeapNode x) {
        x.next = x;
        x.prev = x;
        //can we add x.parent=x.child=null??
    }


    /**
     * Detach x's children list from x and return the head of that list (or null).
     * Also sets each child's parent to null.
     * Does NOT change children's next/prev structure.
     */
    private static HeapNode detachChildren(HeapNode x) {
        if (x == null || x.child == null) return null;

        HeapNode start = x.child;
        HeapNode c = start;

        do {
            c.parent = null;
            c = c.next;
        } while (c != start);

        x.child = null;
        x.rank = 0;   // OK only because we detached all children from x
        return start;
    }


    private static void detachFromList(HeapNode x) {
        if (x == null) return;
        if (x.next == x) return;  // כבר singleton
        HeapNode p = x.prev;
        HeapNode n = x.next;
        p.next = n;
        n.prev = p;
        makeCircular(x);
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
        makeCircular(x);
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
        HeapItem item = new HeapItem();
        item.key = key;
        item.info = info;

        HeapNode node = new HeapNode();
        node.item = item;
        node.rank = 0;
        item.node = node;
        makeCircular(node);

        Heap insert_heap = new Heap(this.lazyMelds, this.lazyDecreaseKeys);
        insert_heap.min = node.item;
        insert_heap.heap_size = 1;
        insert_heap.num_trees = 1;

        this.meld(insert_heap);
        return item;
    }

    /**
     * Return the minimal HeapNode, null if empty.
     */
    public HeapItem findMin() {
        return min;
    }


    public void deleteMin() {
        if (min == null) return;

        HeapNode z = min.node;
        int zRank = z.rank;
        HeapNode childEntry = z.child;

        if (heap_size == 1) {
            min = null;
            heap_size = 0;
            num_trees = 0;
            num_marked_nodes = 0;
            return;
        }

        HeapNode rootsEntry = (z.next != z) ? z.next : null;
        detachFromList(z);

        // להפוך ילדים לשורשים + unmark (כמו שיש לך)
        if (childEntry != null) {
            HeapNode c = childEntry;
            do {
                c.parent = null;
                if (c.marked) { c.marked = false; num_marked_nodes--; }
                c = c.next;
            } while (c != childEntry);
        }

        // ניקוי z (בסדר)
        z.child = null;
        z.parent = null;
        z.rank = 0;
        z.marked = false;

        heap_size--;

        HeapNode entry;
        if (rootsEntry == null) entry = childEntry;
        else {
            entry = rootsEntry;
            if (childEntry != null) entry = concatLists(entry, childEntry);
        }

        //  חדש: עדכון num_trees לפני consolidate
        num_trees = num_trees - 1 + zRank;

        consolidate(entry);
    }




    private void consolidate(HeapNode entry) {
        if (entry == null) {
            min = null;
            return;
        }

        // 1) to-buckets
        HeapNode[] B = toBuckets(entry);

        // 2) from-buckets
        HeapNode newMinNode = fromBuckets(B);

        min = (newMinNode == null) ? null : newMinNode.item;
    }

    private HeapNode[] toBuckets(HeapNode entry) {
        // גודל דליים: מספיק log2(n)+5 (זה upper bound בטוח)
        int max = 1;
        int t = heap_size;
        while (t > 0)
        {
            max++;
            t >>= 1;
        }

        max += 5;

        HeapNode[] B = new HeapNode[max];
        for (int i = 0; i < B.length; i++)
            B[i] = null;

        HeapNode x = entry;
        int roots = num_trees;   // מספר השורשים לפני פירוק הרשימה

        for (int i = 0; i < roots; i++) {
            HeapNode next = x.next;   // next של "הרשימה הישנה" לפני שננתק
            detachFromList(x);        // עכשיו x singleton

            HeapNode y = x;

            while (true) {
                int r = y.rank;
                if (r >= B.length) {
                    HeapNode[] B2 = new HeapNode[r + 10];
                    System.arraycopy(B, 0, B2, 0, B.length);
                    B = B2;
                }
                if (B[r] == null) break;

                HeapNode other = B[r];
                B[r] = null;
                y = link(y, other);
            }

            B[y.rank] = y;

            x = next;
        }


        return B;
    }

    private HeapNode fromBuckets(HeapNode[] B) {
        HeapNode x = null;          // זה יהיה "entry" לרשימת השורשים החדשה
        HeapNode minNode = null;

        int trees = 0;

        for (int i = 0; i < B.length; i++) {
            HeapNode b = B[i];
            if (b == null) continue;

            trees++;

            // אם זו ההתחלה, בונים רשימה חדשה עם b בלבד
            if (x == null) {
                x = b;
                makeCircular(x);
            } else {
                spliceAfter(x, b);   // insert-after(x, B[i]) כמו בשקופית
                // בשקופית: אם B[i].key < x.key אז x <- B[i]
                // אצלנו x זה רק entry, מינימום ננהל בנפרד
            }

            if (minNode == null || b.item.key < minNode.item.key) {
                minNode = b;
            }
        }

        // אם את מנהלת numTrees:
        num_trees = trees;

        return minNode;
    }

    private HeapNode link(HeapNode a, HeapNode b) {
        // נוודא ש-a הוא הקטן
        if (b.item.key < a.item.key) {
            HeapNode tmp = a; a = b; b = tmp;
        }

        // b נהיה ילד של a
        b.parent = a;

        // שורש לא אמור להיות מסומן; אם היה—מבטלים
        if (b.marked) {
            System.out.println("possibly an error, root was marked");
            b.marked = false;
            num_marked_nodes--;
        }

        // הוספת b לרשימת הילדים של a
        if (a.child == null) {
            a.child = b;
            makeCircular(b);
        } else {
            spliceAfter(a.child, b);
        }

        a.rank++;
        total_links++;
        return a;
    }

    //swap 2 items
    private void swapItems(HeapNode a, HeapNode b) {
        // This must be used only in non-lazy decreaseKey mode (heapify-up).
        HeapItem tmp = a.item;
        a.item = b.item;
        b.item = tmp;

        // IMPORTANT: keep back pointers consistent
        a.item.node = a;
        b.item.node = b;
    }

    private void heapifyUp(HeapNode x) {
        while (x.parent != null && x.item.key < x.parent.item.key) {
            swapItems(x, x.parent);
            total_heapify_cost++;   // count swaps as heapify cost
            x = x.parent;           // continue with the item that moved up
        }
    }

    private void removeFromChildList(HeapNode parent, HeapNode x) {
        // x is a child of parent
        if (parent.child == x) {
            if (x.next == x) {
                parent.child = null;
            } else {
                parent.child = x.next;
            }
        }
        detachFromList(x);     // IMPORTANT: our fixed detach (no rank/child touching)
        parent.rank--;
        x.parent = null;
    }

    private void addToRootList(HeapNode x) {
        // x is a singleton circular list at this point
        if (min == null) {
            // theoretically can happen only if heap was empty, but keep safe
            min = x.item;
            num_trees = 1;
            return;
        }
        concatLists(min.node, x);
        num_trees++;
        considerAsMin(x);
    }

    private void cut(HeapNode x, HeapNode parent) {
        removeFromChildList(parent, x);

        // unmark x if needed
        if (x.marked) {
            x.marked = false;
            num_marked_nodes--;
        }

        addToRootList(x);
        total_cuts++;
    }

    private void cascadingCut(HeapNode y) {
        HeapNode z = y.parent;
        if (z == null) {
            // y is a root: roots should not be marked
            if (y.marked) {
                y.marked = false;
                num_marked_nodes--;
            }
            return;
        }

        if (!y.marked) {
            y.marked = true;
            num_marked_nodes++;
        } else {
            cut(y, z);
            cascadingCut(z);
        }
    }



    /**
     * pre: 0<=diff<=x.key
     * <p>
     * Decrease the key of x by diff and fix the heap.
     */

    public void decreaseKey(HeapItem x, int diff) {
        if (x == null || x.node == null || diff <= 0) return;

        x.key -= diff;
        HeapNode node = x.node;

        // always update min candidate
        considerAsMin(node);

        if (!lazyDecreaseKeys) {
            heapifyUp(node);
            // min might have changed via swaps
            considerAsMin(x.node);
            return;
        }

        // lazyDecreaseKeys == true: use cuts
        HeapNode parent = node.parent;
        if (parent == null) return; // node is a root, we're done

        if (node.item.key >= parent.item.key) return; // heap order not violated

        cut(node, parent);
        cascadingCut(parent);
    }


    /**
     * Delete the x from the heap.
     */
    public void delete(HeapItem x) {
        if (x == null || x.node == null || heap_size == 0) return;

        if (min != null && x == min) {
            deleteMin();
            return;
        }

        // Choose a target strictly smaller than current min.key, computed in long to avoid overflow
        long minKey = (min == null) ? 0L : (long) min.key;
        long targetLong = minKey - 1L;

        // Clamp target to int range
        if (targetLong < (long) Integer.MIN_VALUE) targetLong = (long) Integer.MIN_VALUE;

        long diffLong = (long) x.key - targetLong;

        // We need diff > 0 for decreaseKey
        if (diffLong <= 0) {
            // x is already <= target; still try to force it down a bit if possible
            // If x.key == Integer.MIN_VALUE, we can't decrease further in int, but that case
            // is extremely unlikely in the course tests.
            if (x.key == Integer.MIN_VALUE) {
                // fallback: just deleteMin if somehow x became min already, otherwise no-op
                if (min != null && x.key == min.key) deleteMin();
                return;
            }
            diffLong = 1;
        }

        // Clamp diff to int range (diff is expected to be safe in normal test ranges)
        int diff = (diffLong > (long) Integer.MAX_VALUE) ? Integer.MAX_VALUE : (int) diffLong;

        decreaseKey(x, diff);
        deleteMin();
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

        if (!lazyMelds) {
            // After concatenating root lists, do successive linking immediately
            consolidate(this.min.node);   // any root entry is fine; consolidate will rebuild min anyway
        }
    }


    /**
     * Return the number of elements in the heap
     */
    public int size() {
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
        public int rank = 0;
        public boolean marked = false;
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
