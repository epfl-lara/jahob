
/**
 * A class representing a three dimensional vector that implements
 * several math operations.  To improve speed we implement the vector
 * as an array rather than use the exising code in the
 * java.util.Vector class.
 **/
class MathVector
{
    int x;
    int y;
    int z;

    /**
     * Construct an empty 3 dimensional vector for use in Barnes-Hut algorithm.
     **/
    MathVector()
    {
	x = 0;
	y = 0;
	z = 0;
    }

    /**
     * Create a copy of the vector.
     * @return a clone of the math vector
     **/
    public Object clone() 
    {
	MathVector v = new MathVector();
	
	v.x = x;
	v.y = y;
	v.z = z;
      
	return v;
    }

    int getX()
    {
	return x;
    }

    int getY()
    {
	return y;
    }

    int getZ()
    {
	return z;
    }

    void setX(int i)
    {
	x = i;
    }

    void setY(int j)
    {
	y = j;
    }

    void setZ(int k)
    {
	z = k;
    }

    /**
     * Add two vectors and the result is placed in this vector.
     * @param u the other operand of the addition
     **/
    final void addition(MathVector u)
    {
	x = x + u.x;
	y = y + u.y;
	z = z + u.z;
    }
    
    /**
     * Subtract two vectors and the result is placed in this vector.
     * This vector contain the first operand.
     * @param u the other operand of the subtraction.
     **/
    final void subtraction(MathVector u)
    {
	x = x - u.x;
	y = y - u.y;
	z = z - u.z;
    }

    /**
     * Subtract two vectors and the result is placed in this vector.
     * @param u the first operand of the subtraction.
     * @param v the second opernd of the subtraction
     **/
    final void subtract(MathVector u, MathVector v)
    {
	x = u.x - v.x;
	y = u.y - v.y;
	z = u.z - v.z;
    }

    /**
     * Multiply the vector times a scalar.
     * @param s the scalar value
     **/
    final void multScalar(int s)
    {
	x = s * x;
	y = s * y;
	z = s * z;
    }

    /**
     * Multiply the vector times a scalar and place the result in this vector.
     * @param u the vector
     * @param s the scalar value
     **/
    final void multArgScalar(MathVector u, int s)
    {
	x = s * u.x;
	y = s * u.y;
	z = s * u.z;
    }

    /**
     * Divide each element of the vector by a scalar value.
     * @param s the scalar value.
     **/
    final void divScalar(int s)
    {
	x = x / s;
	y = y / s;
	z = z / s;
    }

    /**
     * Return the dot product of a vector.
     * @return the dot product of a vector.
     **/
    final int dotProduct()
    {
	return (x * x) + (y * y) + (z * z);
    }

    /**
     * Add a scalar to each element in the vector and put the
     * result in this vector.
     * @param u a vector
     * @param s the scalar
     **/
    final void addScalar(MathVector u, int s) 
    {
	x = u.x + s;
	y = u.y + s;
	z = u.z + s;
    }
}
