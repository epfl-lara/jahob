class Library {
    public static Set persons;
    public static Set books;
    public static Relation borrows;

    /*:
      public static specvar valid :: bool;
      vardefs "valid == notNull &
                        booksDomain & 
                        personsDomain & 
                        globalPointsTo & 
                        uniqueOwner &
                        availabilityPolicy";

      private static specvar notNull :: bool;
      vardefs "notNull == (persons ~= null & books ~= null & borrows ~= null)";

      private static specvar booksDomain :: bool;
      vardefs "booksDomain == books..Set.content \<subseteq> 
                              (Object.alloc Int Book) \<setminus> {null}";

      private static specvar personsDomain :: bool;
      vardefs "personsDomain == persons..Set.content \<subseteq> 
                                (Object.alloc Int Person) \<setminus> {null}";

      private static specvar globalPointsTo :: bool;
      vardefs "globalPointsTo == 
         (ALL p b. (p,b) : borrows..Relation.content -->
            p : persons..Set.content  &  b : books..Set.content)";

      private static specvar uniqueOwner :: bool;
//      vardefs "uniqueOwner == 
//               (ALL b p1 p2. (p1,b) : borrows..Relation.content &
//                             (p2,b) : borrows..Relation.content --> p1 = p2)";
      vardefs "uniqueOwner == 
               (ALL b. card {p. (p,b) : borrows..Relation.content} <= 1)";

//      private static specvar borrowedBooks :: objset;
//      vardefs "borrowedBooks == {b. EX p. (p,b) : borrows..Relation.content}";

//      private static specvar availableBooks :: objset;
//      vardefs "availableBooks == (books..Set.content \<setminus> borrowedBooks)";

      private static specvar availabilityPolicy :: bool;
      // vardefs "availabilityPolicy == card availableBooks >= card (books..Set.content) div 3";
      vardefs "availabilityPolicy == True";
    */

    // ------------------------------------------------------------
    //              Auxiliary private procedures
    // ------------------------------------------------------------

    public static void msg(String s)
    /*:
      requires "True"
      ensures "Object.alloc = old Object.alloc";
     */
    {
        // System.out.println(s);
    }

    private static Person currentReader(Book b)
    /*: requires "valid & b ~= null & b : books..Set.content"
        ensures "(result = null --> (ALL p. (p,b) ~: borrows..Relation.content)) &
                 (result ~= null --> (result,b) : borrows..Relation.content)";
     */
    {
        Set s = borrows.inverseImage(b);
	Person r;
        if (s.isEmpty()) {
	    r = null;
        } else {
	    r = (Person) s.getOne();
        }
	return r;
    }

    private static Set booksLentTo(Person p)
    /*:
      requires "valid & p ~= null & p : persons..Set.content"
      ensures "result ~= null & result..Set.content = {b. (p,b) : borrows..Relation.content} &
               result ~: old Object.alloc";
     */
    {
        return borrows.image(p);
    }

    // ------------------------------------------------------------
    //              Public procedures
    // ------------------------------------------------------------
    
    public static void initialize()
    /*: modifies valid, books, persons, borrows
        ensures "valid & books..Set.content = {} & persons..Set.content = {}
                       & borrows..Relation.content = {}"
    */
     {
	 books = new Set();
	 persons = new Set();
	 borrows = new Relation();
     }
    
    public static void checkOutBook(Person p, Book b)
    /*: requires "valid & p ~= null & b ~= null & 
                  b : books..Set.content & p : persons..Set.content"
       modifies "borrows..Relation.content", valid
       ensures "valid &
comment ''firstCase''
((ALL p1. (p1,b) ~: old (borrows..Relation.content)) --> 
                   borrows..Relation.content = old (borrows..Relation.content) Un {(p,b)})
              & 
comment ''secondCase''
(EX p1. (p1,b) : old (borrows..Relation.content) --> borrows..Relation.content = old (borrows..Relation.content))"
    */
    {
        if (currentReader(b) == null) {
            borrows.add(p,b);
        } else {
            msg("Sorry, book is not available.");
        }
    }

    public static void checkOutBookBroken(Person p, Book b)
    /*: requires "valid & p ~= null & b ~= null & 
                  b : books..Set.content & p : persons..Set.content"
       modifies "borrows..Relation.content"
       ensures "(EX p1. (p1,b) : old (borrows..Relation.content)) --> borrows..Relation.content = old (borrows..Relation.content)"
    */
    {
        borrows.add(p,b);
    }

    public static void checkOutBook1(Person p, Book b)
    /*: requires "valid & p ~= null & b ~= null & 
                  b : books..Set.content & p : persons..Set.content"
        modifies "borrows..Relation.content"
        ensures "((ALL p1. (p1,b) ~: old borrows..Relation.content) --> 
                    borrows..Relation.content = old (borrows..Relation.content) Un {(p,b)})
               & (EX p1. (p1,b) : old borrows..Relation.content --> borrows..Relation.content = old borrows..Relation.content)"
    */
    {
        Set s = borrows.inverseImage(b);
        if (s.isEmpty()) {
            borrows.add(p,b);
        } else {
            msg("Sorry, book is not available.");
        }
        //: noteThat "valid";
    }

    public static void returnBook(Person p, Book b)
    /*: requires "valid & p ~= null & b ~= null & b : books..Set.content & p : persons..Set.content"
       modifies "borrows..Relation.content"
       ensures "borrows..Relation.content = old (borrows..Relation.content) \<setminus> {(p,b)}"
    */
    {
	Person cr = currentReader(b);
        if (cr==p) {
	    borrows.remove(p, b);
        } else {
	    if (cr == null) {
            msg("This book was not borrowed !");
	    }
	    else {
            msg("Someone else was supposed to have that book!");
	    }
        }
    }

    public static void decommissionBook(Book b)
    /*: requires "valid & b ~= null & b : books..Set.content"
       modifies "borrows..Relation.content", "books..Set.content"
       ensures "books..Set.content = old (books..Set.content) \<setminus> {b} &
                borrows..Relation.content = 
                  old (borrows..Relation.content) \<setminus> {(p1,b1). b1=b}"
    */
    {
	Person p = currentReader(b);
        books.remove(b);
        if (p!=null) {
          borrows.remove(p, b);
        }
    }

    public static void printBooksLentTo(Person p) // requires e:SortGuards=no
	/*: requires "valid & p ~= null & p : persons..Set.content"
            modifies valid
	    ensures "valid"
	*/
    {
	msg("Books lent to person");
	p.print();
	msg("  are: ");
	Set bs = booksLentTo(p);
        //: ghost specvar allocs :: objset = "Object.alloc";
	while /*: inv "valid &
              allocs \<subseteq> Object.alloc &
              (ALL s. s : Set & s : old Object.alloc & s ~= bs --> 
                 s..Set.content = old (s..Set.content)) &
              bs..Set.content \<subseteq> books..Set.content" */ 
            (!bs.isEmpty())
	    {
		Book b = (Book) bs.getOne();
		bs.remove(b);
		b.print();
	    }
    }

    public static void printBooksLentTo1(Person p) // requires e:SortGuards=no
	/*: requires "valid & p ~= null & p : persons..Set.content"
            ensures "True"
	*/
    {
	msg("Books lent to person");
	p.print();
	msg("  are: ");
	Set bs = borrows.image(p);
        //: ghost specvar allocs :: objset = "Object.alloc";
	while /*: inv "valid &
              allocs \<subseteq> Object.alloc &
              (ALL s. s : Set & s : old Object.alloc & s ~= bs --> 
                 s..Set.content = old (s..Set.content)) &
              bs..Set.content \<subseteq> books..Set.content" */ 
            (!bs.isEmpty())
	    {
		Book b = (Book) bs.getOne();
		bs.remove(b);
		b.print();
	    }
    }

    public static void printCurrentReader(Book b)
	/*: requires "valid & b ~= null & b : books..Set.content"
	    ensures "True"
	*/
    {
        Person p = currentReader(b);
        if (p==null) {
            msg("The book is in the library.");
        } else {
            msg("Person ");
            p.print();
            msg("  has checked out the book ");
            b.print();
        }
    }


    public static void printStatus()
	/*: requires "valid"
            modifies valid
	    ensures "valid"
	*/
    {
        Set ps = borrows.domain();
        //: ghost specvar allocs :: objset = "Object.alloc";
	while /*: inv "valid &
              allocs \<subseteq> Object.alloc &
              (ALL s. s : Set & s : old Object.alloc & s ~= ps --> 
                 s..Set.content = old (s..Set.content)) &
              ps..Set.content \<subseteq> persons..Set.content" */ 
            (!ps.isEmpty())
        {
            Person p = (Person)(ps.getOne());
            printBooksLentTo(p);
	    ps.remove(p);
        }
    }
}
