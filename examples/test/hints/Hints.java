// Testing hint annotations
class Hints {
    private static int x;
    private static int y;
    private static int z;
    private static int u;
    
    public static void testEq()
    {
        //: assume xySame: "x = y";
        //: assume yzSame: "y = z";
        //: noteThat xzEqual: "z = x" from xySame, yzSame;
    }

    public static void testPos()
    {
        //: assume xPos: "x > 0";
        //: assume yPos: "y > 0";
        //: assume zSum: "z = x + y";
        //: assert zPos: "z > 0" from xPos, yPos, zSum;
    }

    public static void testPosShort()
    {
        //: assume xPos: "x > 0";
        //: assume yPos: "y > 0";
        //: assume zSum: "z = x + y";
        //: noteThat zPos: "z > 0" from Pos, zS;
    }

    public static void testImpl()
    {
	//: assume xPos: "x > 0";
	//: noteThat impl: "y > 0 --> x + y > 0" from xPos, impl;
    }

    public static void testImplBreaks()
    {
	//: assume xPos: "x > 0";
	//: noteThat impl: "y > 0 --> x + y > 0" from xPos;
    }
}

