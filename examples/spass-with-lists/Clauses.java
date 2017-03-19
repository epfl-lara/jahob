public class Set {
   /*: 
     public specvar content :: "obj set";
     private vardefs "content == {}";
     public ensured invariant "ALL x. x : content --> x : Object.alloc";
   */

   public void remove (Object o)
   /*: modifies "this..content"
     ensures "content = old content - {o}";
    */
   {
      // ...
   }

   public void add (Object o)
   /*: modifies "this..content"
     ensures "content = old content Un {o}";
    */
   {
      // ...
   }
}

public final class Clause {
   /*:
     public specvar literals :: "obj set";
     private vardefs "literals == (literalSet..content)";
     invariant "this ~= null --> literalSet ~= null";
   */

   private Set literalSet;

   public void remove (Literal l)
   /*: modifies "this..literals"
     ensures "literals = old literals - {l}";
   */
   {
      literalSet.remove(l);
   }

   public void add (Literal l)
   /*: modifies "this..literals"
     ensures "literals = old literals Un {l}";
   */
   {
      literalSet.add(l);
   }
}

public final class Variable {

   private Literal hd;

   /*:
     private static specvar reach :: "obj => obj => bool";
     private vardefs "reach == (% x y. (x,y) : {(x, y). x..next = y}^*)";

     public specvar literals :: "obj set";
     private vardefs "literals == {x. x ~= null & reach hd x}";
   
     invariant DLL1: "ALL x. x..prev..next = x | x..prev = null & (ALL y. y..next ~= x)";
     invariant DLL2: "ALL x. x..next..prev = x | x..next = null & (ALL y. y..prev ~= x)";

     invariant "reach hd null";
   */

   public Literal head () 
   /*: ensures "result : literals | literals = {} & result = null"; */  
   {
      return hd;
   }

   public void remove (Literal l)      
   /*: requires "l : literals"
     modifies "this..literals"
     ensures "literals = old literals - {l}";
   */
   {
      //: assume "ALL x y. x : Literal & y : Literal & y ~= null & reach x y --> reach x (y..prev) & y..prev ~= null";
      Literal p = l.prev;
      Literal n = l.next;

      if (n != null) n.prev = p;
      if (p != null) p.next = n;
      else hd = n;

      l.next = null;
      l.prev = null;
   }

   public void add (Literal l)      
   /*: requires "l ~= null & (ALL l1. l1..next ~= l & l1..prev ~= l) & (ALL v. l ~: v..literals)"
     modifies "this..literals"
     ensures "literals = old literals Un {l}";
   */
   {
      //: assume "ALL x y. x : Literal & y : Literal & y ~= null & reach x y --> reach x (y..prev) & y..prev ~= null";
      if (head != null) head.prev = l;
      l.next = hd;
      l.prev = null;
      hd = l;
   }
}

public final class Literal {
   public /*: claimedby Variable */ Literal next;
   public /*: claimedby Variable */ Literal prev;
   public /*: claimedby Clauses */ Variable var;
   public /*: claimedby Clauses */ Clause clause;
   public /*: claimedby Clauses */ boolean sign;
}

public class Clauses 
{
   private static Set clauseSet;

   private static Set varSet;
   private static Set trueVarSet;
   private static Set falseVarSet;

   /*:
     private static ghost specvar currLit :: "obj";
     
     //public static specvar solutions :: "";

     public static specvar clauses :: "obj set";
     private vardefs "clauses == (clauseSet..content)";

     public static specvar vars :: "obj set";
     private vardefs "vars == (varSet..content)";

     public static specvar trueVars :: "obj set";
     private vardefs "trueVars == (trueVarSet..content)";

     public static specvar falseVars :: "obj set";
     private vardefs "falseVars == (falseVarSet..content)";

     public static specvar assignedVars :: "obj set";
     public vardefs "assignedVars == (trueVars Un falseVars)";

     private static specvar invariant1 :: bool;
     private vardefs "invariant1 == (trueVars <= vars)";

     private static specvar invariant2 :: bool;
     private vardefs "invariant2 == (falseVars <= vars)";

     private static specvar invariant3 :: bool;
     private vardefs "invariant3 == (falseVars Int trueVars = {})";

     private static specvar invariant4 :: bool;
     private vardefs "invariant4 == (ALL c l. c : clauses & l : c..Clause.literals --> c..var ~: trueVars & c..var ~: falseVars)";
     
     // disjointness of the sets should already be implied by the representation invariants
     // invariant "ALL v1 v2. v1 : vars & v2 : vars & v1 ~= v2 --> v1..Variable.literals Int v2..Variable.literals = {}";
      
     private static specvar invariant5 :: bool;
     private vardefs "invariant5 == (ALL x. x : clauses --> x : Clause & x ~= null)";

     private static specvar invariant6 :: bool;
     private vardefs "invariant6 == (ALL x. x : vars --> x : Variable & x ~= null)";

     private static specvar invariant7 :: bool;
     private vardefs "invariant7 == (ALL c l. c : clauses & l ~= currLit & l : c..Clause.literals --> l..clause = c & l : l..var..Variable.literals & l..var : vars)";

     private static specvar invariant8 :: bool;
     private vardefs "invariant8 == (ALL v l. v : vars & l ~= currLit & l : v..Variable.literals --> l..var = v & l : l..clause..Clause.literals & l..clause : clauses)";

     private static specvar invariant9 :: bool;
     private vardefs "invariant9 == (ALL l. l ~= currLit & l..clause : clauses --> l : l..clause..Clause.literals)";

     private static specvar invariant10 :: bool;
     private vardefs "invariant10 == (ALL l. l ~= currLit & l..var : vars --> l : l..var..Variable.literals)";

     private static specvar invariant11 :: bool;
     private vardefs "invariant11 == (clauseSet ~= null & varSet ~= null)";

     private static specvar theInvariant :: bool;
     private vardefs "theInvariant == (invariant1 & invariant2 & invariant3 & invariant4 & invariant5 & 
                                       invariant6 & invariant7 & invariant8 & invariant9 & invariant10 & invariant11)";

     public static ghost specvar wrapped :: bool;
     invariant "wrapped --> theInvariant & currLit = null";
   */

   public static void removeLit (Literal l)
   /*: requires "l..clause : clauses"
       modifies "l..clause..Clause.literals", "l..var..Variable.literals"
       ensures "l..clause..Clause.literals = old (l..Clause.literals) - {l} & 
                l..var..Variable.literals = old (l..var..Variable.literals) - {l}";
   */
   {
      Clause c = l.clause;
      c.remove(l);

      Variable v = l.var;
      v.remove(l);

      l.var = null;
      l.clause = null;
   }

   public static void add (boolean s, Variable v, Clause c) 
   /*: requires "v : vars & c : clauses & (ALL l. l : c..Clause.literals --> l..var ~= v)"
     modifies "c..Clause.literals", "v..Variable.literals"
     ensures "EX l. l..sign = s & c..Clause.literals = old (c..Clause.literals) Un {l} & 
              v..Variable.literals = old (v..Variable.literals) Un {l}";
    */
   {
      Literal l = new Literal();
      c.add(l);
      v.add(l);
      l.var = v;
      l.clause = c;
      l.sign = s;
      
   }

   private static void removeClause (Clause c) 
   /*: requires "theInvariant & c : clauses"
     modifies "clauses", "Variable.literals"
     ensures "theInvariant & 
              clauses = old clauses - {c} &
	      currLit = old currLit &
              (ALL v. v : vars --> v..Variable.literals = old (v..Variable.literals) - old (c..Clause.literals))";
   */
   {
   }

   public static void setVar (Variable v, boolean b)
   /*: requires "wrapped & v : vars & (b --> v ~: falseVars) & (~b --> v ~: trueVars)"
     modifies "clauses", "Set.content", "trueVars", "falseVars", "assignedVars", "Clause.literals", "Variable.literals", "vars"
     ensures "wrapped";
    */
   {
      //: wrapped := "False";
      Literal l = v.head();
      while /*: inv "v : vars & ~wrapped & theInvariant & currLit = null &
	             (l : v..Variable.literals | l = null & v..Variable.literals = {})" */
	 (l != null) {
	 Clause c = l.clause;
	 
	 if (l.sign == b) {
	    removeClause(l.clause);
	 } else {
	    //: currLit := "l";
	    c.remove(l);
	    v.remove(l);
	    l.clause = null;
	    l.var = null;
	    //: currLit := "null";
	 }
	 l = v.head();
      }
      //: wrapped := "True";
   }

   
}
 
