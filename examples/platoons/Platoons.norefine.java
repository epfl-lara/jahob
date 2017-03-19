class Car {
   public int state;
   public Car ldr;
   /*:
     public ghost specvar buffer :: objset;
     public ghost specvar flwrs :: objset;
   */
}


class Message {
   Car car;
   int type;
}

class Platoons {

   /*:
     // shortcut definitions
     private static specvar leaders :: objset;
     private static specvar followers :: objset;

     private vardefs "leaders == {x. x..state = 1}";
     private vardefs "followers == {x. x..state = 2}";
     
     private static specvar new_ldr_messages :: objset;
     private static specvar new_flwr_messages :: objset;

     private vardefs "new_ldr_messages == {x. x..type = 0}";
     private vardefs "new_flwr_messages == {x. x..type = 1}";
 
   */
   
   public static void world()
   /*:
     modifies Car, Message, flwrs, state, ldr, buffer, type, car
     ensures "True";
    */
   {
      //: static ghost specvar cars :: objset; 
      //: static ghost specvar messages :: objset;

      //: static ghost specvar tmp_buffer :: "obj => objset";

      //: cars := "{}";
      //: messages := "{}";

      Car activeCar, receiverCar;
      Message m, m2;
      boolean b;

      //: static specvar buf :: "(obj * obj) set";
      //: vardefs "buf == {(x,y). x : y..buffer}";
      //: static specvar ccars :: "(obj * obj) set";
      //: vardefs "ccars == {(x,y). y : cars} :: (obj * obj) set";
      //: static specvar tbuf :: "(obj * obj) set";
      //: vardefs "tbuf == {(x,y). x : y..tmp_buffer}";
      //: static specvar cactiveCar :: "(obj * obj) set";
      //: vardefs "cactiveCar == {(x,y). activeCar = y} :: (obj * obj) set";
      //: static specvar creceiverCar :: "(obj * obj) set";
      //: vardefs "creceiverCar == {(x,y). receiverCar = y} :: (obj * obj) set";
      //: static specvar cm :: "(obj * obj) set";
      //: vardefs "cm == {(x,y). m = y} :: (obj * obj) set";
      //: static specvar cm2 :: "(obj * obj) set";
      //: vardefs "cm2 == {(x,y). m2 = y} :: (obj * obj) set";
      //: static specvar cflwrs :: "(obj * obj) set";
      //: vardefs "cflwrs == {(x,y). x : y..flwrs}";
      //: static specvar cflwrs :: "(obj * obj) set";
      //: vardefs "cflwrs == {(x,y). x : y..flwrs}";
      //: static specvar activeCarflwrs :: "(obj * obj) set";
      //: vardefs "activeCarflwrs == {(x,y). y : activeCar..flwrs} :: (obj * obj) set";
      //: static specvar activeCarbuffer :: "obj set";
      //: vardefs "activeCarbuffer == {x. x : activeCar..buffer}";
      //: static specvar ccar :: "(obj * obj) set";
      //: vardefs "ccar == {(x,y). y..car = x}";
      //: static specvar mcar :: "obj set";
      //: vardefs "mcar == {x. m..car = x}";
      //: static specvar cmessages :: "(obj * obj) set";
      //: vardefs "cmessages == {(x,y). y : messages} :: (obj * obj) set";
      //: static specvar cnew_flwr_messages :: "(obj * obj) set";
      //: vardefs "cnew_flwr_messages == {(x,y). y : new_flwr_messages} :: (obj * obj) set";
      //: static specvar cleaders :: "(obj * obj) set";
      //: vardefs "cleaders == {(x,y). y : leaders} :: (obj * obj) set";
      //: static specvar cfollowers :: "(obj * obj) set";
      //: vardefs "cfollowers == {(x,y). y : followers} :: (obj * obj) set";
      //: static specvar p__activeCar :: obj;
      //: vardefs "p__activeCar == activeCar";
      //: static specvar p__receiverCar :: obj;
      //: vardefs "p__receiverCar == receiverCar";
      //: static specvar p__m2 :: obj;
      //: vardefs "p__m2 == m2";
      //: static specvar p__m :: obj;
      //: vardefs "p__m == m";

      //: track(buf);
      //: track(ccars);
      
      while 
	 /*
	   inv "(ALL c. c : cars & c : leaders --> c..flwrs <= followers & c..flwrs <= cars) &
	        (ALL m. m : messages & m : new_flwr_messages --> m..car : followers & m..car : cars) &
		(ALL c. c : cars --> c..buffer <= messages)"
	  */
	 (true) {
	 //: track(buf);
	 //: track(ccars);
	 //: track(cactiveCar);
	 // track(creceiverCar);
	 //: track(cflwrs);
	 //: track(ccar);
	 //: track(mcar);
	 //: track(cm);
	 //: track(cmessages);
	 //: track(cnew_flwr_messages);
	 //: track(cleaders);
	 //: track(p__activeCar);
	 //: track(p__receiverCar);
	 // the property we verify
	 // assert "ALL c. c : cars --> c..buffer <= messages";
	 //: assert "ALL c. c : cars & c : leaders --> c..flwrs <= followers";
	 // assert "ALL m. m : messages & m : new_flwr_messages --> m..car : followers & m..car : cars";
	 int action;
	 //: havoc action;
	 //: havoc activeCar, receiverCar, m, m2;
	 //: assume "action : {0,1,2,3}";
	  if (action == 3) {
	    // Choose some car in "cars" to perform a step
	    //: assume "activeCar : cars";
            //: b := "activeCar..buffer = {}";
	    if (!b) {
	       // There is some message in the buffer: pick one and remove it
	       //: assume "m : activeCar..buffer";
	       //: assume "m : messages";
	       //: "activeCar..buffer" := "activeCar..buffer - {m}";

	       //: b := "activeCar : followers";
	       if (b) {
		  //: b := "m..type = 0";
		  if (b) {
		     // m : new_ldr_messages

		     // Accept new leader
		     //: "activeCar..ldr" := "m..car";
		     
		     // Send new_flwr message to new leader
		     //: assume "m2 ~: messages";
		     //: messages := "messages Un {m2}";
		     //: "m2..type" := "1";
		     //: "m2..car" := "activeCar";
		     //: "activeCar..ldr..buffer" := "activeCar..ldr..buffer Un {m2}";
		  }
	       } else {
		  //: assume "activeCar : leaders";
		  //: b := "m..type = 1";
		  if (b) {
		     // m : new_flwr_messages

		     //: "activeCar..flwrs" := "activeCar..flwrs Un {m..car}";  
		  } else {
		     //: b := "m..type = 0";
		     if (b) {
			// m : new_leader_messages

			// Broadcast m to all followers
			//: tmp_buffer := "buffer";
			//: havoc buffer;

			// Accept new leader
			//: "activeCar..ldr" := "m..car";
			//: "activeCar..state" := "2";

			//: track(ccars);
			//: track(tbuf);
			//: track(cactiveCar);
			//: track(cflwrs);
			//: track(cm2);
			//: track(p__m);
			//: track(ccar);
			//: track(cmessages);
			//: track(cnew_flwr_messages);
			//: track(cleaders);
			//: track(cfollowers);
	 
			//: assume "ALL x. x ~: activeCar..flwrs --> x..buffer = x..tmp_buffer";
			//: assume "ALL x. x : activeCar..flwrs --> x..buffer = x..tmp_buffer Un {m}";
			
			// Remove links to all followers
			//: "activeCar..flwrs" := "{}";

			// Send new_flwr message to new leader
			//: assume "m2 ~: messages";
			//: messages := "messages Un {m2}";
			//: "m2..type" := "1";
			//: "m2..car" := "activeCar";
			//: "activeCar..ldr..buffer" := "activeCar..ldr..buffer Un {m2}";
		     }
		  }
	       }
	    }
	  } else if (action == 2) {
	    // Choose sender and receiver of new_ldr message
	    //: assume "activeCar : cars Int leaders";
	    //: assume "receiverCar : cars Int leaders";
	    //: assume "activeCar..buffer = {}";
	    //: assume "receiverCar..buffer = {}";
	    //: assume "activeCar ~= receiverCar";

	    // Create message
	    //: assume "m ~: messages";
	    //: assume "m..type = 0";
	    //: assume "m..car = activeCar";
	    //: messages := "messages Un {m}";

	    // Send message
	    //: "receiverCar..buffer" := "receiverCar..buffer Un {m}";
	 } else if (action == 1) {
	    // Remove some free agent
	    //: assume "activeCar : cars";
	    //: assume "activeCar : leaders";
	    //: assume "activeCar..buffer = {}";
	    //: assume "activeCar..flwrs = {}";
	    //: assume "ALL c m. c : cars & m : c..buffer --> m..car ~= activeCar"; 
	    //: cars := "cars - {activeCar}";
	 } else if (action == 0) {
	    // Create new car
	    //: assume "activeCar ~: cars";
	    //: cars := "cars Un {activeCar}";
	    //: "activeCar..buffer" := "{}";
	    //: "activeCar..flwrs" := "{}";
	    //: "activeCar..state" := "1";
	 }
      }
   }
}
