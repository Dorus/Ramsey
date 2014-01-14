package ramsey;

public class Tupel implements Comparable<Tupel> {
	public final int a;
	public final int b;

	Tupel(int a, int b) {
		this.a = a;
		this.b = b;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof Tupel) {
			Tupel ob = (Tupel) obj;
			return this.a == ob.a && this.b == ob.b;
		} else {
			return false;
		}
	}
	
	public boolean equals(int a, int b) {
		return this.a == a && this.b == b;
	}

	@Override
	public int compareTo(Tupel t) {
		if (a == t.a) {
			return Integer.signum(b - t.b);
		}
		return Integer.signum(a - t.a);
	}
	
	public String toString() {
		return "(" + a + ", " + b + ")";
	}
	
	public int hashCode() {
		return a*1000+b;
	}
}
