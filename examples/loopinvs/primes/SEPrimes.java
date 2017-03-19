// implements the Sieve of Eratosthenes algorithm for generating prime
// numbers up to a maximum integer n
class SEPrimes {
    
    static IntSet primes = new IntSet();


    public static void main(String[]args) {
	int n = Integer.parseInt(args[0]);
	computePrimes(n);
	printPrimes();
    }
    
    static void computePrimes(int n) {
	IntSet toProcess = new IntSet();
	int i = 2;
	
	while (i <= n) {
	    toProcess.add(i);
	    i = i + 1;
	}
	
	while(!toProcess.isEmpty()) {
	    int j = toProcess.removeMin();
	    
	    primes.add(j);

	    int k  = j * j;
	    
	    while(k <= n) {
		toProcess.remove(k);
		k = k + j;
	    }
	}
    }

    static void printPrimes() {
	while(!primes.isEmpty()) {
	    int i = primes.removeMin();
	    System.out.print(i + " ");
	}
	System.out.println("");
    }
}
