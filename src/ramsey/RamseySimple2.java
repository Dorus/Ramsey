package ramsey;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;

public class RamseySimple2 {

	public static void main(String[] args) throws IOException {
		try {
			runProgram(args);
		} catch (NumberFormatException e) {
			System.out.println("Usage: Ramsey [nodes] [red] [blue] [ignore] [filename]");
		}
	}

	private static void runProgram(String[] args) throws IOException {
		RamseySimple2 r = new RamseySimple2();

		r.nodes = 6;
		r.red = 5;
		r.blue = 5;
		File file = parseParams(args, r);

		createEquals(r);

		r.write(file);
	}

	private static void createEquals(RamseySimple2 r) {
		ArrayList<ArrayList<Tupel>> a = new ArrayList<ArrayList<Tupel>>();
		for (int j = 1; j <= r.nodes / 2; j++) { // j = 1..nodes/2
			ArrayList<Tupel> b = new ArrayList<Tupel>();
			for (int i = 0; i < r.nodes; i++) { // i = 0 .. nodes - 1
				if (r.nodes % 2 == 0 && j == r.nodes / 2 && i == r.nodes / 2) {
					break;
				}
				if (i > (i + j) % r.nodes) {
					b.add(new Tupel((i + j) % r.nodes, i));
				} else {
					b.add(new Tupel(i, (i + j) % r.nodes));
				}
			}
			a.add(b);
		}
		r.equals = a;
	}

	private static File parseParams(String[] args, RamseySimple2 r) {
		if (args.length > 0) {
			r.nodes = Integer.parseInt(args[2]);
		}

		if (args.length > 1) {
			r.red = Integer.parseInt(args[0]);
		}

		if (args.length > 2) {
			r.blue = Integer.parseInt(args[1]);
		}

		if (args.length > 4) {
			return new File(args[4]);
		} else {
			return new File("smt" + r.red + "_" + r.blue + "_" + r.nodes + ".smt"); // new
																																							// File("C:\\Users\\User\\Dropbox\\uni\\ResA3\\test.smt");
		}
	}

	public void write(File file) throws IOException {
		long startTime = System.currentTimeMillis();

		if (file.exists())
			if (!file.delete()) {
				System.out.println("cant delete file " + file.getAbsolutePath());
				System.exit(1);
			}

		file.createNewFile();
		writer = new PrintWriter(file);

		writeFile();
		writer.flush();
		System.out.println("Time = " + (System.currentTimeMillis() - startTime));
	}

	public ArrayList<ArrayList<Tupel>> equals;
	public int nodes;
	public int red;
	public int blue;
	public PrintWriter writer;

	private void makeForumlas() {
		if (equals != null) {
			eqBuilder();
		}
		formBuilder(0, red, new ArrayList<Integer>(), false);
		formBuilder(0, blue, new ArrayList<Integer>(), true);
	}

	private void eqBuilder() {
		for (ArrayList<Tupel> eq : equals) {
			writer.print("\n(= ");
			for (int i = 0; i < eq.size() - 1; i++) {
				writer.print("(p" + eq.get(i).a + "_" + eq.get(i).b + ") ");
			}
			writer.print(")");
		}
	}

	private void formBuilder(int start, int depth, List<Integer> list, boolean neg) {
		if (depth == 0) {
			makeFormula(list, neg);
		} else {
			for (Integer i = start; i <= (nodes - depth); i++) {
				list.add(i);
				formBuilder(i + 1, depth - 1, list, neg);
				list.remove(i);
			}
		}
	}

	private void makeFormula(List<Integer> list, boolean neg) {
		writer.print("\n(not (and");
		for (int i = 0; i < list.size() - 1; i++) {
			int n1 = list.get(i);
			point: for (int j = i + 1; j < list.size(); j++) {
				int n2 = list.get(j);
				ArrayList<ArrayList<Tupel>> eq = equals;
				for (ArrayList<Tupel> e : eq) {
					int k;
					for (k = 0; k < e.size(); k++) {
						Tupel t = e.get(k);
						if (t.equals(n1, n2)) {
							break;
						}
					}
					k++;
					for (; k < e.size(); k++) {
						Tupel t = e.get(k);
						if (list.contains(t.a) && list.contains(t.b)) {
							continue point;
						}
					}
				}
				if (neg) {
					writer.print(" (not (p" + n1 + "_" + n2 + "))");
				} else {
					writer.print(" (p" + n1 + "_" + n2 + ")");
				}
			}
		}
		writer.print(")) ; ");
		for (Integer i : list) {
			writer.print("," + i);
		}
	}

	private void makePreds() {
		for (int i = 0; i < (nodes - 1); i++) {
			writer.print("\n");
			for (int j = i + 1; j < nodes; j++) {
				writer.print(" (p" + i + "_" + j + ")");
			}
		}
	}

	private void writeFile() {
		writer.print("(benchmark ramsey.smt\n; Find counterexample for ramsey (" + red + ", " + blue + ") with " + nodes
				+ " nodes\n" //
				+ ":extrapreds (");
		makePreds();
		writer.print("\n)\n" //
				+ ":formula\n(and");

		makeForumlas();

		writer.print("\n))");
	}
}
