public class RefCountObject {

   private RefCountObject car, cdr;

   private int count;

   /*:
     private specvar refs :: objset; 
     private vardefs "refs == {x. x..car = this}";
     
     invariant "this ~= null --> count = cardinality refs";
    */

   public void setCarTo(RefCountObject o)
   {
      /*: 
	specvar car_refs :: objset; 
	vardefs "car_refs == (car..refs)";
	specvar o_refs :: objset; 
	vardefs "o_refs == (o..refs)";
	specvar old_car_refs :: objset; 
	vardefs "old_car_refs == old car_refs";
	specvar old_o_refs :: objset; 
	vardefs "old_o_refs == old o_refs";
	specvar p_car :: obj; 
	vardefs "p_car == car";
	//track (car_refs);
	//track (o_refs);
	track (p_car);
	//track (old_car_refs);
	//track (old_o_refs);
       */

      if (car != null)
	 car.count = car.count - 1;
      car = o;
      if (car != null)
	 car.count = car.count + 1;
      // noteThat "old (car..refs) = (old car)..refs Un {this}";
      // noteThat "o..refs = (old o..refs) Un {this}";
   }

}