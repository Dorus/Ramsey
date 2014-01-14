package ramsey;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

public class RamseySimple5 {

	public static void main(String[] args) throws IOException {
		try {
			runProgram(args);
		} catch (NumberFormatException e) {
			System.out.println("Usage: Ramsey [nodes] [red] [blue] [filename]");
		}
	}

	private static void runProgram(String[] args) throws IOException {
		RamseySimple5 r = new RamseySimple5();

		r.nodes = 42;
		r.red = 5;
		r.blue = 6;
		File file = parseParams(args, r);

		r.write(file);
	}

	private static File parseParams(String[] args, RamseySimple5 r) {
		if (args.length > 0) {
			r.red = Integer.parseInt(args[0]);
		}
		if (args.length > 1) {
			r.blue = Integer.parseInt(args[1]);
		}
		if (args.length > 2) {
			r.nodes = Integer.parseInt(args[2]);
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

	public int nodes;
	public int red;
	public int blue;
	public PrintWriter writer;

	private void makeForumlas() {
		new Builder5(this, new ArrayList<Integer>(), false).formBuilder(red);
		new Builder5(this, new ArrayList<Integer>(), true).formBuilder(blue);
	}

	private void makePreds() {
		for (int i = 1; i <= nodes / 2; i++) {
			writer.print("\n");
			writer.print(" (p" + i + ")");
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

class Builder5 {
	List<Integer> list;
	boolean neg;
	RamseySimple5 rams;

	public Builder5(RamseySimple5 rams, List<Integer> list, boolean neg) {
		this.rams = rams;
		this.list = list;
		this.neg = neg;
	}

	void formBuilder(int depth) {
		list.add(0);
		formBuilder(1, depth - 1);
		list.remove(0);
	}

	private void formBuilder(int start, int depth) {
		if (depth <= 0) {
			makeFormula();
		} else {
			for (Integer i = start; i <= (rams.nodes - depth); i++) {
				list.add(i);
				formBuilder(i + 1, depth - 1);
				list.remove(i);
			}
		}
	}

	private Set<Integer> formulaList = new TreeSet<Integer>();
	private Set<Set<Integer>> formulsLists = new HashSet<Set<Integer>>();

	private void makeFormula() {
		for (int i = 0; i < list.size() - 1; i++) {
			for (int j = i + 1; j < list.size(); j++) {
				int edge = (0 - Math.abs((list.get(j) - list.get(i)) * 2 - rams.nodes) + rams.nodes) / 2;
				if (!formulaList.contains(edge)) {
					formulaList.add(edge);
				}
			}
		}
		if (!formulsLists.contains(formulaList)) {
			formulsLists.add(new TreeSet<Integer>(formulaList));
			rams.writer.print("\n(not (and");
			for (Integer t : formulaList) {
				if (neg) {
					rams.writer.print(" (not (p" + t + "))");
				} else {
					rams.writer.print(" (p" + t + ")");
				}
			}
			rams.writer.print("));");
		}
		formulaList.clear();
	}
}
