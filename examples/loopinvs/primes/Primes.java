// a parallelizable algorithm for generating prime numbers up to a
// maximum integer n

class Primes {
    
    static IntSet primes;
    static IntSet worklist;

    public static void main(String[]args) {
	//int n = Integer.parseInt(args[0]);
	int n = 100;
	computePrimes(n);
	printPrimes();
    }
    
    static void computePrimes(int n) {
	initialize(n);
	
	// main loop
	while(!worklist.isEmpty()) {
	    processOne();
	}
    }

    static void initialize(int n) {
	primes = new IntSet();
	worklist = new IntSet();
	
	int i = 2;

	while (i <= n) {
	    worklist.add(i);
	    i = i + 1;
	}
    }

    static void processOne() {
	int i = worklist.extractOne();
	
	if (isPrime(i)) primes.add(i);
    }

    static boolean isPrime(int i) {
	int j = 2;

	//while (j <= (int)Math.sqrt((double)i)) {
	while (j < i) {
	    if (i % j == 0) {
		return false;
	    }
	    j = j + 1;
	}
	return true;
    }

    static void printPrimes() {
    }
    /*
	while(!primes.isEmpty()) {
	    int i = primes.removeMin();
	    System.out.print(i + " ");
	}
	System.out.println("");
    }
    */
}
