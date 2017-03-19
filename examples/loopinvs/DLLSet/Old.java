public class Datum {
    int x;
}

public class Old {

    public static void old()
    //: ensures "True"
    {
        int i = 0;
        int arrSz = 10;
        Datum[] dArr = new Datum[arrSz];

        while (i < arrSz) {
            dArr[i] = new Datum();
            dArr[i].x = i;
            i = i + 1;
        }

        testBegin(dArr);
    }

    public static void testBegin(Datum[] dArr0)
    {
        // test0: first increment in caller
        // merge involves dropping entry from callee
        Datum d0 = dArr0[0];
        d0.x = d0.x + 1;
        incrementD2x(d0);
        //: assert "d0..Datum.x = (fieldRead (old Datum.x) d0) + 3";

        // test1: first increment in callee
        // merge involves keeping entry from callee
        Datum d1 = dArr0[1];
        incrementD2x(d1);
        //: assert "d1..Datum.x = (fieldRead (old Datum.x) d1) + 2";

        // test2: null out entry at index in caller then create new in callee
        // merge involves dropping entry from callee
        Datum d2 = dArr0[2];
        dArr0[2] = null;
        //: assert "arrayRead (old Array.arrayState) dArr0 2 = d2";
        //: assert "dArr0.[2] = null";
        createNewAt(dArr0, 2);
        //: assert "arrayRead (old Array.arrayState) dArr0 2 = d2";
        //: assert "dArr0.[2] ~= d2";
        //: assert "dArr0.[2]..Datum.x = 0";

        // test3: null out entry at index in callee
        // merge involves keeping entry from callee
        Datum d3 = dArr0[3];
        nullAt(dArr0, 3);
        //: assert "arrayRead (old Array.arrayState) dArr0 3 = d3";
        //: assert "dArr0.[3] = null";
        
    }

    public static void incrementD2x(Datum d)
    {
        d.x = d.x + 1;
        //: assert "d..Datum.x = (fieldRead (old Datum.x) d) + 1";
        d.x = d.x + 1;
        //: assert "d..Datum.x = (fieldRead (old Datum.x) d) + 2";
    }

    public static void createNewAt(Datum[] dArr1, int index)
    {
        Datum dindex = dArr1[index];
        dArr1[index] = new Datum();
        //: assert "arrayRead (old Array.arrayState) dArr1 index = dindex";
    }

    public static void nullAt(Datum[] dArr2, int index)
    {
        Datum dindex = dArr2[index];
        dArr2[index] = null;
        //: assert "arrayRead (old Array.arrayState) dArr2 index = dindex";
    }
}
