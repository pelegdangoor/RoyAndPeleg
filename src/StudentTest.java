public class StudentTest {

    public static void main(String[] args) {
        String[] failedTests = new String[4];
        int failCount = 0;
        int totalPoints = 100;
        int pointsPerTest = totalPoints / 4;
        int score = 0;

        if (testInsertAndFindMin()) {
            score += pointsPerTest;
        } else {
            failedTests[failCount++] = "Test1: Insert and findMin";
        }

        if (testDeleteMin()) {
            score += pointsPerTest;
        } else {
            failedTests[failCount++] = "Test2: deleteMin";
        }

        if (testDecreaseKey()) {
            score += pointsPerTest;
        } else {
            failedTests[failCount++] = "Test3: decreaseKey";
        }

        if (testDeleteNode()) {
            score += pointsPerTest;
        } else {
            failedTests[failCount++] = "Test4: delete specific node";
        }

        System.out.println("Grade: " + score + " / " + totalPoints);
        if (failCount > 0) {
            System.out.println("Failed tests:");
            for (int i = 0; i < failCount; i++) {
                System.out.println("  - " + failedTests[i]);
            }
        } else {
            System.out.println("All tests passed!");
        }
    }

    private static boolean testInsertAndFindMin() {
        Heap heap = new Heap(true, true);
        heap.insert(10, "A");
        heap.insert(5, "B");
        heap.insert(20, "C");
        return heap.findMin() != null && heap.findMin().key == 5;
    }

    private static boolean testDeleteMin() {
        Heap heap = new Heap(true, true);
        heap.insert(10, "A");
        heap.insert(5, "B");
        heap.insert(20, "C");
        heap.deleteMin();
        return heap.findMin() != null && heap.findMin().key == 10;
    }

    private static boolean testDecreaseKey() {
        Heap heap = new Heap(true, true);
        heap.insert(30, "X");
        heap.insert(40, "Y");
        Heap.HeapNode n3 = heap.insert(50, "Z");
        heap.decreaseKey(n3, 25); // new key = 25
        return heap.findMin() != null && heap.findMin().key == 25;
    }

    private static boolean testDeleteNode() {
        Heap heap = new Heap(true, true);
        heap.insert(15, "P");
        Heap.HeapNode n2 = heap.insert(7, "Q");
        heap.insert(25, "R");
        heap.delete(n2);
        return heap.findMin() != null && heap.findMin().key == 15;
    }
}
