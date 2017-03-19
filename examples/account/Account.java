class Account {
    private static int checkingBalance;
    private static int savingsBalance;

    private static void checkingDeposit(int amount)
    /*:
      requires "amount > 0"
      modifies checkingBalance
      ensures "checkingBalance = old checkingBalance + amount"
     */
    {
	checkingBalance = checkingBalance + amount;
    }

    private static void checkingWithdraw(int amount)
    /*:
      requires "amount > 0 & checkingBalance >= amount"
      modifies checkingBalance
      ensures "checkingBalance = old checkingBalance - amount"
     */
    {
	checkingBalance = checkingBalance - amount;
    }

    private static void savingsDeposit(int amount)
    /*:
      requires "amount > 0"
      modifies savingsBalance
      ensures "savingsBalance = old savingsBalance + amount"
     */
    {
	savingsBalance = savingsBalance + amount;
    }

    private static void transferSavingsToChecking(int amount)
    /*:
      requires "amount > 0 & savingsBalance >= amount"
      modifies checkingBalance, savingsBalance
      ensures "savingsBalance = old savingsBalance  - amount &
               checkingBalance = old checkingBalance + amount"
     */
    {
	savingsBalance = savingsBalance - amount;
	checkingBalance = checkingBalance + amount;
    }

    private static void transferCheckingToSavings(int amount)
    /*:
      requires "amount > 0 & checkingBalance >= amount"
      modifies checkingBalance, savingsBalance
      ensures "checkingBalance = old checkingBalance - amount &
               savingsBalance  = old savingsBalance  + amount"
     */
    {
	checkingWithdraw(amount);
	savingsDeposit(amount);
    }
}
