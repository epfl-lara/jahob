class Elem {
    public /*: claimedby Students */ Elem attends;
    public /*: claimedby Students */ Elem next;
}
class Students {
    private static Elem students;
    private static Elem schools;

    /*:
      private static specvar reach :: "obj => obj => bool";
      vardefs "reach == (% a b. rtrancl_pt (% x y. x..Elem.next = y) a b)";

      public static specvar ST :: objset;
      vardefs "ST == {x. x ~= null & reach students x}";
      public static specvar SC :: objset;
      vardefs "SC == {x. x ~= null & reach schools x}";

      public invariant "null ~: (ST Un SC)";
      public invariant "ST Int SC = {}";

      invariant "tree [Elem.next]";
      invariant "ALL x y. Elem.attends x = y -->
                   (x : ST --> y : SC) &
                   (x ~: ST --> y = null)";

      invariant "ALL x. x ~: (ST Un SC Un {null}) --> 
                        (ALL y. y ~= null --> y..Elem.next~=x) &
                        x..Elem.next=null";
     */

    public static void addStudent(Elem st, Elem sc)
    /*:
      requires "st ~: (ST Un SC Un {null}) & sc : SC"
      modifies ST
      ensures "ST = old ST Un {st}"
     */
    {
        st.attends = sc;
        st.next = students;
        students = st;
    }
}
