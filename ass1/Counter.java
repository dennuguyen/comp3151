public class Counter {
    public static void main(String[] args) {
        if (args.length != 3) {
            throw  new IllegalArgumentException("Unexpected number of arguments.");
        }
    }
}