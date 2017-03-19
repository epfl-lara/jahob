public class Datum {
    int x;
}

public class Aliasing {
    
    public static void aliasing()
    //: ensures "True"
    {
	Datum d1 = new Datum();
	Datum d2 = d1;
	
	//: assert "d1..Datum.x = 0";
	
	modify_and_check(d1, d2);
    }

    public static void modify_and_check(Datum e1, Datum e2)
    {
	e1.x = 7;

	//: assert "fieldRead (old Datum.x) (old e1) = 0";
	//: assert "fieldRead (old Datum.x) (old e2) = 0";
    }
    
}
