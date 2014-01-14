package ramsey;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;

public class RamseySimple4 {

	public static void main(String[] args) throws IOException {
		try {
			runProgram(args);
		} catch (NumberFormatException e) {
			System.out.println("Usage: Ramsey [nodes] [red] [blue] [ignore] [filename]");
		}
	}

	private static void runProgram(String[] args) throws IOException {
		RamseySimple4 r = new RamseySimple4();

		r.nodes = 9;
		r.red = 4;
		r.blue = 4;
		File file = parseParams(args, r);

		r.createEquals();

		r.write(file);
	}

	public Map<Tupel, Tupel> equalsMap;

	private void createEquals() {
		equalsList = new ArrayList<ArrayList<Tupel>>();
		equalsMap = new HashMap<Tupel, Tupel>(nodes * nodes);
		for (int j = 1; j <= nodes / 2; j++) { // j = 1..nodes/2
			ArrayList<Tupel> b = new ArrayList<Tupel>();
			Tupel firstEdge = new Tupel(0, j);
			b.add(firstEdge);
			for (int i = 1; i < nodes; i++) { // i = 0 .. nodes - 1
				if (nodes % 2 == 0 && j == nodes / 2 && i == nodes / 2) {
					break;
				}
				if (i > (i + j) % nodes) {
					equalsMap.put(new Tupel((i + j) % nodes, i), firstEdge);
					b.add(new Tupel((i + j) % nodes, i));
				} else {
					equalsMap.put(new Tupel(i, (i + j) % nodes), firstEdge);
					b.add(new Tupel(i, (i + j) % nodes));
				}
			}
			equalsList.add(b);
		}
	}

	private static File parseParams(String[] args, RamseySimple4 r) {
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

	public ArrayList<ArrayList<Tupel>> equalsList;
	public int nodes;
	public int red;
	public int blue;
	public PrintWriter writer;

	private void makeForumlas() {
		if (equalsList != null) {
			eqBuilder();
		}
		new Builder4(this, new ArrayList<Integer>(), false).formBuilder(0, red);
		new Builder4(this, new ArrayList<Integer>(), true).formBuilder(0, blue);
	}

	private void eqBuilder() {
		for (ArrayList<Tupel> eq : equalsList) {
			writer.print("\n(= ");
			for (int i = 0; i < eq.size() - 1; i++) {
				writer.print("(p" + eq.get(i).a + "_" + eq.get(i).b + ") ");
			}
			writer.print(")");
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

class Builder4 {
	List<Integer> list;
	boolean neg;
	RamseySimple4 rams;

	public Builder4(RamseySimple4 rams, List<Integer> list, boolean neg) {
		this.rams = rams;
		this.list = list;
		this.neg = neg;
	}

	void formBuilder(int start, int depth) {
		if (depth == 0) {
			makeFormula();
		} else {
			for (Integer i = start; i <= (rams.nodes - depth); i++) {
				list.add(i);
				formBuilder(i + 1, depth - 1);
				list.remove(i);
			}
		}
	}

	private TreeSet<Tupel> formulaList = new TreeSet<Tupel>();
	private ArrayList<TreeSet<Tupel>> formulsLists = new ArrayList<TreeSet<Tupel>>();

	private void makeFormula() {
		for (int i = 0; i < list.size() - 1; i++) {
			int n1 = list.get(i);
			for (int j = i + 1; j < list.size(); j++) {
				int n2 = list.get(j);
				Tupel t = new Tupel(n1, n2);
				Tupel edge = rams.equalsMap.get(t);
				if(edge == null) {
					edge = t;
				}
				if (!formulaList.contains(edge)) {
					formulaList.add(edge);
				}
			}
		}
		if (!formulsLists.contains(formulaList)) {
			TreeSet<Tupel> l = new TreeSet<Tupel>();
			l.addAll(formulaList);
			formulsLists.add(l);
			rams.writer.print("\n(not (and");
			for (Tupel t : formulaList) {
				if (neg) {
					rams.writer.print(" (not (p" + t.a + "_" + t.b + "))");
				} else {
					rams.writer.print(" (p" + t.a + "_" + t.b + ")");
				}
			}
			rams.writer.print("));//");
			for (int i : list) {
				rams.writer.print("," + i);
			}
		}
		formulaList.clear();
	}
}
