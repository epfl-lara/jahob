class Object {
    private final int hashCode;

    /*: public static ghost specvar alloc :: objset = "{null}";

        public static specvar hashFunc :: "(obj \<Rightarrow> int)";
	vardefs "hashFunc == (\<lambda> o1. o1..hashCode)";

	invariant hCInv: "hashCode = hashFunc this";
    */

    public int hashCode()
    /*: ensures "result = hashFunc this \<and> alloc = old alloc"
     */
    {
	return hashCode;
    }
}
