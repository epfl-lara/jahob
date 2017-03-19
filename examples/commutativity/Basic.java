class Basic {

    public int sum = 0;

    private void sum (int add)
    /*:
      modifies sum
      ensures "sum = old sum + add & Object.alloc = old Object.alloc"
     */
    {
        sum = sum + add;
    }

    public void sum2 (int x, int y, int z, int t)
    /*:
      modifies sum
      ensures "sum = old sum + x + y + z + t & Object.alloc = old Object.alloc"
     */
    {
        sum(x);
        sum = sum + y;
        sum(z);
        sum = sum + t;
    }
}