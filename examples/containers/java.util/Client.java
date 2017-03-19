public class Data {
   public boolean value;
}

public class Client {

   public static void createMove()
   /*: 
     modifies "Set.content", "Iterator.content"
     ensures "True"
   */
   {
      Set s1 = new Set();
      boolean nondet;
      while (nondet) {
	 //: havoc nondet;
	 Object o = new Object();
	 s1.add(o);
      }

      //: ghost specvar oldContent :: objset = "s1..Set.content";
      Set s2 = new Set();
      Iterator i = s1.iterator();
      while (i.hasNext()){
	 Object oa = i.next();
	 s1.remove(oa);
	 s2.add(oa);
      }
      //: assert "s2..Set.content = oldContent";
   }

   public static void createErase() 
   {
      Set s = new Set();
      boolean nondet;
      while (nondet) {
	 //: havoc nondet;
	 Object o = new Object();
	 s.add(o);
      }

      Iterator i = s.iterator();
      
      while (i.hasNext()) {
	 Object oa = i.next();
	 s.remove(oa);
      }

      //: assert "s..Set.content = {}";
   }

   public static void erase(Set s) 
   /*: 
     requires "s ~= null"
     modifies "s..Set.content", "Iterator.content"
     ensures "s..Set.content = {}"
   */
   {
      Iterator i = s.iterator();
      
      while (i.hasNext()) {
	 Object oa = i.next();
	 s.remove(oa);
      }
   }

   public static void move(Set s1, Set s2) 
   /*: 
     requires "s1 ~= null & s2 ~= null & s1 ~= s2"
     modifies "Set.content", "Iterator.content"
     ensures "True"
   */
   /* 
     requires "s1 ~= null & s2 ~= null & s1 ~= s2"
     modifies "s1..Set.content", "s2..Set.content", "Iterator.content"
     ensures "s1..Set.content = {} & s2..Set.content = old (s1..Set.content) Un old (s2..Set.content)"
   */
   {
      Iterator i = s1.iterator();
      
      while (i.hasNext()) {
	 Object oa = i.next();
	 s1.remove(oa);
	 s2.add(oa);
      }
   }

   public static void partition(Set s)
   /*: 
     requires "s ~= null & s..Set.content \<subseteq> Data & s..Set.content Int {null} = {}"
     modifies "Set.content", "Iterator.content"
     ensures "True";
   */
      
   {
      Set s1 = new Set();
      Set s2 = new Set();
      Iterator i = s.iterator();

      while(i.hasNext()){
	 Data d = i.next();
	 if(d.value) s1.add(d);
	 else s2.add(d);
      }

      //: assert "s1..Set.content Int s2..Set.content = {}";
      // assert "s1..Set.content \<subseteq> {x. x..Data.value}";
   }

}