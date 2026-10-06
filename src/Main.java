// Assignment 1 - Myers' diff (Java)
//
//   java Main lines     A B   -> minimal line diff from A to B
//   java Main highlight A B   -> same, plus "? old | new" changed character ranges for each paired line
//
// If a file cannot be read: nothing on stdout, a message on stderr, exit code 2.

import java.io.BufferedOutputStream;
import java.io.FileDescriptor;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.HashMap;

public class Main {

    static class FileLines {
        final byte[] content;
        final int[] start;
        final int[] end;
        final int count;

        // Split raw bytes on '\n'. A final '\n' does not add an empty line, and '\r' stays part of the line.
        FileLines(byte[] content) {
            this.content = content;
            int n = 0;
            for (byte c : content) if (c == '\n') n++;
            if (content.length > 0 && content[content.length - 1] != '\n') n++;
            count = n;
            start = new int[n];
            end = new int[n];

            int line = 0;
            int lineStart = 0;
            for (int pos = 0; pos < content.length; pos++) {
                if (content[pos] == '\n') {
                    start[line] = lineStart;
                    end[line++] = pos;
                    lineStart = pos + 1;
                }
            }
            if (lineStart < content.length) {
                start[line] = lineStart;
                end[line] = content.length;
            }
        }

        int length(int line) {
            return end[line] - start[line];
        }

        // ISO-8859-1 maps every byte to exactly one char, so keys are equal only when the bytes are equal.
        String key(int line) {
            return new String(content, start[line], length(line), StandardCharsets.ISO_8859_1);
        }

        // An emoji is one code point even though Java stores it as two chars.
        int[] codePoints(int line) {
            return new String(content, start[line], length(line), StandardCharsets.UTF_8).codePoints().toArray();
        }
    }

    // Equal lines in either file get the same id, so the diff only compares ints.
    static int[] toIds(FileLines file, HashMap<String, Integer> ids) {
        int[] result = new int[file.count];
        for (int i = 0; i < file.count; i++) {
            result[i] = ids.computeIfAbsent(file.key(i), k -> ids.size());
        }
        return result;
    }

    // Linear-space Myers (paper, section 4b): find the middle snake, split there, recurse on both halves.
    // Each half needs at most half the edits, so recursion depth is only O(log D).
    static class MyersDiff {
        private final int[] a;
        private final int[] b;
        final boolean[] deleted;
        final boolean[] inserted;

        // V[k] is stored at index k + offset because k can be negative.
        private final int[] forward;
        private final int[] backward;
        private final int offset;
        private int splitX;
        private int splitY;

        MyersDiff(int[] a, int[] b) {
            this.a = a;
            this.b = b;
            deleted = new boolean[a.length];
            inserted = new boolean[b.length];
            int maxD = (a.length + b.length + 1) / 2 + 1;
            offset = maxD + 1;
            forward = new int[2 * maxD + 3];
            backward = new int[2 * maxD + 3];
        }

        MyersDiff compute() {
            diff(0, a.length, 0, b.length);
            return this;
        }

        private void diff(int aLo, int aHi, int bLo, int bHi) {
            while (aLo < aHi && bLo < bHi && a[aLo] == b[bLo]) {
                aLo++;
                bLo++;
            }
            while (aLo < aHi && bLo < bHi && a[aHi - 1] == b[bHi - 1]) {
                aHi--;
                bHi--;
            }
            if (aLo == aHi) {
                Arrays.fill(inserted, bLo, bHi, true);
                return;
            }
            if (bLo == bHi) {
                Arrays.fill(deleted, aLo, aHi, true);
                return;
            }
            findMiddleSnake(aLo, aHi, bLo, bHi);
            int x = aLo + splitX;
            int y = bLo + splitY;
            diff(aLo, x, bLo, y);
            diff(x, aHi, y, bHi);
        }

        private void findMiddleSnake(int aLo, int aHi, int bLo, int bHi) {
            int n = aHi - aLo;
            int m = bHi - bLo;
            int delta = n - m;
            boolean deltaOdd = (delta & 1) != 0;
            int maxD = (n + m + 1) / 2;
            forward[offset + 1] = 0;
            backward[offset + 1] = 0;

            for (int d = 0; d <= maxD; d++) {
                for (int k = -d; k <= d; k += 2) {
                    int x = startX(forward, k, d);
                    int y = x - k;
                    while (x < n && y < m && a[aLo + x] == b[bLo + y]) {
                        x++;
                        y++;
                    }
                    forward[offset + k] = x;

                    // Odd delta: paths can only meet after a forward step.
                    // Forward diagonal k is backward diagonal (delta - k); backward has finished d - 1 rounds.
                    int kb = delta - k;
                    if (deltaOdd && kb >= -(d - 1) && kb <= d - 1 && x + backward[offset + kb] >= n) {
                        splitX = x;
                        splitY = y;
                        return;
                    }
                }

                // Backward search: x and y count the distance from the END of a and b.
                for (int k = -d; k <= d; k += 2) {
                    int x = startX(backward, k, d);
                    int y = x - k;
                    while (x < n && y < m && a[aHi - 1 - x] == b[bHi - 1 - y]) {
                        x++;
                        y++;
                    }
                    backward[offset + k] = x;

                    // Even delta: paths can only meet after a backward step.
                    int kf = delta - k;
                    if (!deltaOdd && kf >= -d && kf <= d && x + forward[offset + kf] >= n) {
                        splitX = n - x;
                        splitY = m - y;
                        return;
                    }
                }
            }
            throw new IllegalStateException("middle snake not found");
        }

        // Step down from diagonal k+1 (insert) or right from k-1 (delete), whichever got further.
        private int startX(int[] v, int k, int d) {
            boolean down = k == -d || (k != d && v[offset + k - 1] < v[offset + k + 1]);
            return down ? v[offset + k + 1] : v[offset + k - 1] + 1;
        }
    }

    // A line that exists in only one file can never be kept, so mark it directly and run Myers
    // only on the shared lines. The result is still minimal, but much faster when many lines changed.
    static void diffLines(int[] a, int[] b, int idCount, boolean[] deleted, boolean[] inserted) {
        boolean[] inA = new boolean[idCount];
        boolean[] inB = new boolean[idCount];
        for (int id : a) inA[id] = true;
        for (int id : b) inB[id] = true;

        int[] sharedA = sharedIndices(a, inB);
        int[] sharedB = sharedIndices(b, inA);
        MyersDiff core = new MyersDiff(idsAt(a, sharedA), idsAt(b, sharedB)).compute();

        Arrays.fill(deleted, true);
        Arrays.fill(inserted, true);
        for (int i = 0; i < sharedA.length; i++) deleted[sharedA[i]] = core.deleted[i];
        for (int j = 0; j < sharedB.length; j++) inserted[sharedB[j]] = core.inserted[j];
    }

    static int[] sharedIndices(int[] ids, boolean[] inOther) {
        int[] result = new int[ids.length];
        int n = 0;
        for (int i = 0; i < ids.length; i++) {
            if (inOther[ids[i]]) result[n++] = i;
        }
        return Arrays.copyOf(result, n);
    }

    static int[] idsAt(int[] ids, int[] indices) {
        int[] result = new int[indices.length];
        for (int i = 0; i < indices.length; i++) result[i] = ids[indices[i]];
        return result;
    }

    // Marks to ranges with exclusive end, e.g. [no, yes, yes, no, yes] -> "1-3,4-5"; nothing marked -> "."
    static String ranges(boolean[] marked) {
        StringBuilder sb = new StringBuilder();
        int pos = 0;
        while (pos < marked.length) {
            if (!marked[pos]) {
                pos++;
                continue;
            }
            int rangeStart = pos;
            while (pos < marked.length && marked[pos]) pos++;
            if (sb.length() > 0) sb.append(',');
            sb.append(rangeStart).append('-').append(pos);
        }
        return sb.length() == 0 ? "." : sb.toString();
    }

    static String highlightLine(int[] oldChars, int[] newChars) {
        MyersDiff d = new MyersDiff(oldChars, newChars).compute();
        return "? " + ranges(d.deleted) + " | " + ranges(d.inserted) + "\n";
    }

    static void writeLine(OutputStream out, char prefix, FileLines file, int line) throws IOException {
        out.write(prefix);
        out.write(file.content, file.start[line], file.length(line));
        out.write('\n');
    }

    static void printDiff(FileLines fileA, FileLines fileB, boolean[] deleted, boolean[] inserted,
                          boolean highlight, OutputStream out) throws IOException {
        int i = 0;
        int j = 0;
        while (i < fileA.count || j < fileB.count) {
            boolean changed = (i < fileA.count && deleted[i]) || (j < fileB.count && inserted[j]);
            if (!changed) {
                writeLine(out, ' ', fileA, i++);
                j++;
                continue;
            }

            int iEnd = i;
            while (iEnd < fileA.count && deleted[iEnd]) iEnd++;
            int jEnd = j;
            while (jEnd < fileB.count && inserted[jEnd]) jEnd++;

            // Delete-first rule: every "-" line of the block before any "+" line.
            for (int p = i; p < iEnd; p++) writeLine(out, '-', fileA, p);
            for (int q = j; q < jEnd; q++) {
                writeLine(out, '+', fileB, q);
                int pair = i + (q - j);   // the k-th "+" line is paired with the k-th "-" line
                if (highlight && pair < iEnd) {
                    String line = highlightLine(fileA.codePoints(pair), fileB.codePoints(q));
                    out.write(line.getBytes(StandardCharsets.US_ASCII));
                }
            }
            i = iEnd;
            j = jEnd;
        }
    }

    public static void main(String[] args) throws IOException {
        OutputStream out = new BufferedOutputStream(new FileOutputStream(FileDescriptor.out), 1 << 16);
        int exitCode = run(args, out, System.err);
        out.flush();
        if (exitCode != 0) System.exit(exitCode);
    }

    // Separate from main so tests can call it directly. Returns 0 on success, 2 on any input error.
    static int run(String[] args, OutputStream out, PrintStream err) throws IOException {
        boolean validCommand = args.length == 3 && (args[0].equals("lines") || args[0].equals("highlight"));
        if (!validCommand) {
            err.println("usage: java Main lines|highlight A B");
            return 2;
        }

        // Read both files before printing anything, so a bad file leaves stdout empty.
        FileLines fileA;
        FileLines fileB;
        try {
            fileA = new FileLines(Files.readAllBytes(Paths.get(args[1])));
            fileB = new FileLines(Files.readAllBytes(Paths.get(args[2])));
        } catch (IOException | RuntimeException e) {
            err.println("cannot read input file: " + e);
            return 2;
        }

        HashMap<String, Integer> ids = new HashMap<>();
        int[] idsA = toIds(fileA, ids);
        int[] idsB = toIds(fileB, ids);

        boolean[] deleted = new boolean[fileA.count];
        boolean[] inserted = new boolean[fileB.count];
        diffLines(idsA, idsB, ids.size(), deleted, inserted);
        printDiff(fileA, fileB, deleted, inserted, args[0].equals("highlight"), out);
        return 0;
    }
}