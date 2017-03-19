class BookStoreSaleCustomerSegment {
    private static BookStoreValueNetwork bookstore;
    private static Customer customer;
/*: 
    public static ghost specvar  wanted_spec :: " obj => obj ";
    public static ghost specvar  wanted_book :: " obj => obj ";
*/
    private static void SaleAction (PartNumber wanted_pn)
    /*:
      requires "(wanted_pn ~= null) --> ((wanted_spec wanted_pn): bookstore..BookStoreValueNetwork.catalog..Set.content) &
      ((wanted_spec wanted_pn)..BookSpec.pn = wanted_pn) &

      (((wanted_book (wanted_spec wanted_pn)) : bookstore..BookStoreValueNetwork.inventory..Set.content) & 
      (wanted_spec wanted_pn = (wanted_book (wanted_spec wanted_pn)..Book.spec))) &

      (customer..Customer.cash..Cash.v >= (wanted_book (wanted_spec wanted_pn)..Book.spec..BookSpec.price..Price.v))"

      modifies "bookstore..BookStoreValueNetwork.cash..Cash.v", 
               "bookstore..BookStoreValueNetwork.inventory",
               "customer..Customer.cash..Cash.v", "customer..Customer.bookShelf"
      
      ensures "(bookstore..BookStoreValueNetwork.cash..Cash.v = old (bookstore..BookStoreValueNetwork.cash..Cash.v) + 
                  (wanted_spec wanted_pn)..BookSpec.price..Price.v) &

               (bookstore..BookStoreValueNetwork.inventory..Set.content = 
                   old (bookstore..BookStoreValueNetwork.inventory..Set.content) \<setminus>
                   {(wanted_book (wanted_spec wanted_pn))}) &

               (customer..Customer.cash..Cash.v = old (customer..Customer.cash..Cash.v) - 
                  (wanted_spec wanted_pn)..BookSpec.price..Price.v) &

               (customer..Customer.bookShelf..Set.content = old (customer..Customer.bookShelf..Set.content) Un 
                  {(wanted_book (wanted_spec wanted_pn))})"
     */
    {
	BookSpec bs =  bookstore.getSpec(wanted_pn);
	Book b = bookstore.getBook(bs);

	bookstore.cash.v = bookstore.cash.v +bs.price.v;
	customer.cash.v = customer.cash.v - bs.price.v;

	Set.remove(b,bookstore.inventory);
	Set.insert(b,customer.bookShelf);
    }

 }
///////////////////////////////////////////
/////////BOOKSTORE/////////////////////////
///////////////////////////////////////////

class BookStoreValueNetwork {
    Set inventory; //set of Book
    /*
      invariant inventoryOfBooks: "inventory..Set.content \<subseteq> Book" */
    Set  catalog; // set of BookSpec
    /*
      invariant catalogOfSpecs: "catalog..Set.content \<subseteq> BookSpec" */
    Cash cash;
    /*
      invariant positiveCash: "cash>=0" */

    // inventory is not empty
    // each book in inventory is described by its spec
    /* 
      invariant nonemptyinv: "inventory \<noteq> null \<and> inventory..Set.size >0";
      invariant eachBookHasSpec: "ALL b. b\<in> inventory..Set.content --> 
      (\<exists> bs. bs\<in> catalog..Set.content \<and> b..Book.spec = bs)"
    */

    public BookSpec getSpec(PartNumber pn)
    /*: requires "pn ~= null"
	ensures "(result : catalog..Set.content) & (result..BookSpec.pn = pn)"
    */

{
	//: assume "False"
	catalog.initIter();
        BookSpec curSpec = (BookSpec)catalog.nextIter();
	while (curSpec != null) { 
	    if (curSpec.pn == pn) return curSpec;
	    else curSpec = (BookSpec)catalog.nextIter(); 
	}
	return null;
    }   
   
    public Book getBook(BookSpec bs)
    /*: requires "bs ~= null"
	ensures "(result : inventory..Set.content) & (result..Book.spec = bs)"
*/
    {
        //: assume "False"
	inventory.initIter();
        Book curBook = (Book)inventory.nextIter();
	while (curBook != null) { 
	    if (curBook.spec == bs) return curBook;
	    else curBook = (Book)inventory.nextIter(); 
	}
	return null;
    }    
}

///////////////////////////////
/////CUSTOMER//////////////////
///////////////////////////////
class Customer {
    PartNumber wantedPN;
    Set bookShelf; //set of books
 /*
      invariant shelfOfBooks: "shelf..Set.content \<subseteq> Book" 
 */
    public Message message;
    public Cash cash;
}


//--------------------------------------
class Book{
    BookSpec spec;
}

class BookSpec{
    Price price;//Price
    PartNumber pn;//PartNumber

}
////////////////////////////////////////////////
///////////PRIMITIVE CLASSES////////////////////
////////////////////////////////////////////////

class Price{
    int  v;
}
class Cash{
    int v;
}
class PartNumber{
    String v;
}

class Message {
    //notification message
    boolean v;
}

