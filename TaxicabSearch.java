

import java.io.IOException;
import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

/**
 * FASE B - ricerca di Ta(7) con seed strutturati, RIPRENDIBILE tra un lancio e l'altro.
 *
 * IDEA. Ogni intero si scrive in modo unico come N = M^3 * s con s libero da cubi.
 * Da N = 2m(m^2+3h^2) i fattori di m^2+3h^2 (m,h coprimi) sono 3 oppure primi = 1 (mod 3).
 * Il Ta(7) noto e' 670236^3 * s0, s0 = 7*13*19*43*73*97*157 (sette primi = 1 mod 3).
 * Si esplorano quindi i seed s SQUAREFREE, prodotto di >= MIN_PRIMES_IN_SEED primi
 * di PRIMES, con S_MIN <= s <= S_MAX. Per ogni seed si provano TUTTI gli M da 2 fino a
 * cbrt(bound/s) (oltre, N supererebbe il bound noto: inutile). Per ogni (s,M) il test
 * e' ESATTO (mediane m = mu*d, mu | M^3, d | s; divisibilita' + quadrato perfetto).
 * E' un'euristica sulla famiglia dei seed: NON e' una ricerca esaustiva di Ta(7).
 *
 * COME FUNZIONA IL "RILANCIO". La famiglia viene generata e ORDINATA in modo
 * deterministico (per costo crescente: prima i seed con M massimo piccolo). Ogni seed ha
 * un INDICE fisso 0..N-1. Un lancio elabora una fetta contigua di indici e, se non sei in
 * modalita' "fetta manuale", salva in CHECKPOINT_FILE l'indice da cui ripartire.
 * Il salvataggio avviene dopo ogni "batch" (BATCH_STEPS passi), quindi se interrompi il
 * programma perdi al massimo un batch.
 *
 * ===== COME IMPOSTARE I RANGE (vedi le costanti nella sezione 2) =====
 *  A) Uso normale, automatico: START_INDEX_OVERRIDE = -1. Ogni lancio riprende dal
 *     checkpoint (o da 0 la prima volta) ed esegue circa RUN_STEP_BUDGET passi.
 *     Basta rilanciare il main() finche' non stampa "FAMIGLIA COMPLETATA".
 *     Per lanci a tempo (es. la notte) usa MAX_RUN_MINUTES: il lancio si ferma dopo il
 *     primo batch che supera il limite (RUN_STEP_BUDGET resta come tetto di lavoro).
 *  B) Fetta manuale: START_INDEX_OVERRIDE >= 0 (e END_INDEX, esclusivo). Il lancio
 *     elabora SOLO [START, END) e NON legge ne' scrive il checkpoint: utile per test o per
 *     dividere il lavoro tra piu' macchine (ognuna con la sua fetta e i suoi file).
 *  C) Test rapido: il programma stampa l'indice del seed s0 del Ta(7) noto. Imposta
 *     START = quell'indice, END = START+1: deve trovare N = bound noto con M=670236.
 *
 * REGOLA D'ORO: non cambiare PRIMES, MIN_PRIMES_IN_SEED, S_MIN, S_MAX tra un lancio e
 * l'altro dello stesso ciclo: gli indici cambierebbero significato. Il checkpoint contiene
 * una "impronta" della famiglia e il programma si rifiuta di proseguire se non coincide.
 * Per esplorare un'altra famiglia (altri primi, altro intervallo) cambia anche
 * CHECKPOINT_FILE e RESULTS_FILE (o cancella il vecchio checkpoint).
 *
 * I risultati (N con >= 7 rappresentazioni) vengono aggiunti a RESULTS_FILE.
 * Nessun argomento da riga di comando. Richiede Java 16+.
 */
public class TaxicabSearch {


    // ============ 1) DEFINIZIONE DELLA FAMIGLIA (non cambiare tra i lanci) ============
    static final int[] PRIMES = {
        7, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283,  // vecchi
        307, 313, 331, 337, 349, 367, 373, 379, 397	// nuovi
    };
    static final int OLD_PRIMES_COUNT = 28;
    static final int MIN_PRIMES_IN_SEED = 4;
    static final int MAX_PRIMES_IN_SEED = 4;
    static final long S_MIN = 10_000_000_000L;          // 1e10
    static final long S_MAX = 1_000_000_000_000_000L;   // 1e15

    // ============ 2) CONTROLLO DEL SINGOLO LANCIO (modificabile a ogni lancio) ============
    // NOTA: queste costanti sono i valori di default (uso a mano da IDE). Da riga di comando
    // (GitHub Actions) vengono sovrascritte dai parametri "run" / "plan" (vedi main).
    static long START_INDEX_OVERRIDE = -1;              // -1 = riprendi dal checkpoint; >=0 = fetta manuale
    static long END_INDEX = Long.MAX_VALUE;             // esclusivo; MAX_VALUE = fino a fine famiglia
    static long RUN_STEP_BUDGET = 10_000_000_000L;      // passi M massimi per questo lancio
    static double MAX_RUN_MINUTES = 0;                  // 0 = nessun limite di tempo; >0 = stop a fine batch utile
    static final long BATCH_STEPS = 10_000_000L;         // granularita' di checkpoint / controllo tempo
    static final String STATUS_FILE = "status.txt";     // scritto a fine lancio (DONE / INCOMPLETE nextIndex=...)
    static final String CHECKPOINT_FILE = "checkpoint_" + PRIMES[0] + "_" + PRIMES[PRIMES.length - 1] + "_minmax" + MIN_PRIMES_IN_SEED + ".txt";
    static final String RESULTS_FILE = "hits_" + PRIMES[0] + "_" + PRIMES[PRIMES.length - 1] + "_minmax" + MIN_PRIMES_IN_SEED + ".txt";

    // ============ costanti del problema ============
    static final int TARGET_WAYS = 7;
    static final BigInteger CURRENT_BEST = new BigInteger("24885189317885898975235988544");
    static final long M0 = 670236L;                                 // Ta(7) noto = M0^3 * S0

    public static void main(String[] args) throws Exception {
        // ---- famiglia ordinata deterministicamente ----
        List<long[]> fam = new ArrayList<>();               // {s, maschera primi, mLimit}
        genSeeds(0, 1L, 0, 0L, fam);
        fam.sort((x, y) -> x[2] != y[2] ? Long.compare(x[2], y[2]) : Long.compare(x[0], y[0]));
        int n = fam.size();
        long[] cum = new long[n + 1];                        // passi cumulati (M=2..mLimit => mLimit-1 passi)
        for (int i = 0; i < n; i++) cum[i + 1] = cum[i] + Math.max(0, fam.get(i)[2] - 1);
        String fingerprint = "primes=" + Arrays.toString(PRIMES) + ";oldPrimesCount=" + OLD_PRIMES_COUNT
                + ";minPrimes=" + MIN_PRIMES_IN_SEED + ";maxPrimes=" + MAX_PRIMES_IN_SEED
                + ";sMin=" + S_MIN + ";sMax=" + S_MAX + ";size=" + n + ";steps=" + cum[n];

        // ---- parametri da riga di comando ----
        //   plan <passiPerJob> [da] [a]     -> stampa su stdout la matrice JSON {"include":[{"start":..,"end":..},..]}
        //   run  <start> <end> [maxMinuti]  -> elabora la fetta [start,end) (modalita' fetta manuale)
        if (args.length >= 2 && args[0].equals("plan")) {
            long perJob = Long.parseLong(args[1].trim());
            // args[2] (opzionale): intervalli "a-b,c-d" di indici da pianificare; vuoto = tutta la famiglia
            List<int[]> ranges = new ArrayList<>();
            if (args.length > 2 && !args[2].isBlank()) {
                for (String r : args[2].trim().split("\\s*,\\s*")) {
                    String[] ab = r.split("-");
                    ranges.add(new int[]{Integer.parseInt(ab[0].trim()), (int) Math.min(Long.parseLong(ab[1].trim()), n)});
                }
            } else ranges.add(new int[]{0, n});
            printPlan(cum, ranges, perJob);
            return;
        }
        if (args.length >= 3 && args[0].equals("run")) {
            START_INDEX_OVERRIDE = Long.parseLong(args[1]);
            END_INDEX = Long.parseLong(args[2]);
            RUN_STEP_BUDGET = Long.MAX_VALUE;
            if (args.length > 3) MAX_RUN_MINUTES = Double.parseDouble(args[3]);
        }

        System.out.println("START " + PRIMES[0] + "_" + PRIMES[PRIMES.length - 1] + "_minmax" + MIN_PRIMES_IN_SEED);
        System.out.println("Seed nella famiglia: " + n + "   passi totali: " + String.format("%,d", cum[n]));

        // ---- fetta di questo lancio ----
        boolean sliceMode = START_INDEX_OVERRIDE >= 0;
        long start;
        if (sliceMode) {
            start = START_INDEX_OVERRIDE;
            System.out.println("Modalita': FETTA MANUALE (il checkpoint non viene ne' letto ne' scritto)");
        } else {
            Long cp = readCheckpoint(fingerprint);
            start = (cp == null) ? 0 : cp;
            System.out.println("Modalita': AUTOMATICA. " + (cp == null ? "Nessun checkpoint: parto da 0."
                : "Checkpoint trovato: riprendo dall'indice " + start + "."));
        }
        long end = Math.min(END_INDEX, (long) n);
        if (start >= end) {
            System.out.println(sliceMode ? "Fetta vuota." : "FAMIGLIA COMPLETATA: nessun altro seed da elaborare.");
            return;
        }
        System.out.println("Fetta: indici [" + start + ", " + end + ")   passi disponibili: "
            + String.format("%,d", cum[(int) end] - cum[(int) start]) + "   budget di questo lancio: "
            + String.format("%,d", RUN_STEP_BUDGET));

        // ---- crivello (dimensionato sul massimo M realmente necessario) ----
        long maxM = Math.max(fam.get(n - 1)[2], M0);
        int[] spf = buildSpf((int) maxM);

        // ---- ciclo a batch ----
        int cores = Runtime.getRuntime().availableProcessors();
        ExecutorService pool = Executors.newFixedThreadPool(cores);
        System.out.println("Core: " + cores);
        long t0 = System.nanoTime();
        long idx = start, stepsThisRun = 0;
        int hitsThisRun = 0;

        while (idx < end && stepsThisRun < RUN_STEP_BUDGET) {
            // costruisci il batch: seed contigui [idx, j)
            int j = (int) idx;
            long batchSteps = 0;
            while (j < end) {
                long st = cum[j + 1] - cum[j];
                boolean first = (j == idx);
                if (!first && (batchSteps + st > BATCH_STEPS || stepsThisRun + batchSteps + st > RUN_STEP_BUDGET)) break;
                batchSteps += st;
                j++;
            }
            // limite di tempo: non iniziare un batch che, alla velocita' attuale, sforerebbe MAX_RUN_MINUTES
            if (MAX_RUN_MINUTES > 0 && stepsThisRun > 0) {
                double elapsed = (System.nanoTime() - t0) / 1e9;
                double estBatch = batchSteps / (stepsThisRun / Math.max(elapsed, 1e-9));
                if (elapsed + estBatch > MAX_RUN_MINUTES * 60) {
                    System.out.println("Limite di tempo (" + MAX_RUN_MINUTES + " min) raggiunto: mi fermo prima del prossimo batch.");
                    break;
                }
            }
            final int from = (int) idx, to = j;

            ConcurrentLinkedQueue<Object[]> hits = new ConcurrentLinkedQueue<>();
            List<Future<?>> futs = new ArrayList<>();
            for (int i = from; i < to; i++) {
                final long[] f = fam.get(i);
                final int seedIndex = i;
                futs.add(pool.submit(() -> {
                    Map<BigInteger, Integer> fac = new TreeMap<>();
                    for (int b = 0; b < PRIMES.length; b++)
                        if ((f[1] >> b & 1L) != 0) fac.put(BigInteger.valueOf(PRIMES[b]), 1);
                    BigInteger sv = BigInteger.valueOf(f[0]);
                    BigInteger[] dv = divisorsSorted(fac);
                    for (long m = 2; m <= f[2]; m++) {
                        List<BigInteger[]> reps = searchRepresentations(m, sv, dv, spf);
                        if (reps.size() >= TARGET_WAYS)
                            hits.add(new Object[]{seedIndex, sv, m, BigInteger.valueOf(m).pow(3).multiply(sv), reps});
                    }
                }));
            }
            for (Future<?> fu : futs) fu.get();

            for (Object[] h : hits) { reportHit(h); hitsThisRun++; }
            idx = to;
            stepsThisRun += batchSteps;
            if (!sliceMode) writeCheckpoint(fingerprint, idx, cum[(int) idx]);

            double sec = (System.nanoTime() - t0) / 1e9;
            double rate = stepsThisRun / Math.max(sec, 1e-9);
            System.out.printf("  batch [%d,%d)  passi run: %,d  |  famiglia: %.2f%% (indice %d/%d)  |  %.0f passi/s  |  trovati nel run: %d%n",
                from, to, stepsThisRun, 100.0 * cum[(int) idx] / cum[n], idx, n, rate, hitsThisRun);
        }
        pool.shutdown();

        double sec = (System.nanoTime() - t0) / 1e9;
        System.out.println();
        System.out.printf("=== Fine lancio: %,d passi in %.0f s (%.0f passi/s) ===%n", stepsThisRun, sec, stepsThisRun / Math.max(sec, 1e-9));
        System.out.println("Risultati di questo lancio: " + hitsThisRun + "  (elenco in " + RESULTS_FILE + ")");
        long remaining = cum[(int) end] - cum[(int) idx];
        try {
            Files.writeString(Paths.get(STATUS_FILE), (idx >= end ? "DONE" : "INCOMPLETE") + " start=" + start + " end=" + end
                + " next=" + idx + " hits=" + hitsThisRun + "\n", StandardCharsets.UTF_8);
        } catch (IOException e) {
            System.out.println("(attenzione: impossibile scrivere " + STATUS_FILE + ": " + e.getMessage() + ")");
        }
        if (idx >= end) {
            System.out.println(sliceMode ? "Fetta completata."
                : "FAMIGLIA COMPLETATA: tutti i " + n + " seed sono stati esplorati.");
        } else {
            double rate = stepsThisRun / Math.max(sec, 1e-9);
            System.out.println("PROSSIMO LANCIO riparte dall'indice " + idx + (sliceMode ? " (imposta START_INDEX_OVERRIDE a questo valore)" : " (automatico da checkpoint)"));
            System.out.printf("Passi ancora da fare nella fetta: %,d  (~%.1f ore alla velocita' di questo lancio)%n", remaining, remaining / rate / 3600.0);
        }
    }

    // ---------------- piano delle fette (modalita' "plan") ----------------

    /** Spezza [from,to) in fette contigue di ~perJob passi ciascuna e stampa la matrice JSON per GitHub Actions.
     *  Una matrice puo' avere al massimo 256 job: se servono di piu', perJob viene alzato automaticamente. */
    static void printPlan(long[] cum, List<int[]> ranges, long perJob) {
        List<long[]> slices;
        long total = 0;
        for (int[] r : ranges) total += cum[r[1]] - cum[r[0]];
        while (true) {
            slices = new ArrayList<>();
            for (int[] r : ranges) {
                int a = r[0], to = r[1];
                while (a < to) {
                    int b = a + 1;
                    while (b < to && cum[b + 1] - cum[a] <= perJob) b++;
                    slices.add(new long[]{a, b});
                    a = b;
                }
            }
            if (slices.size() <= 256) break;
            perJob = (long) (perJob * 1.1) + 1;
        }
        StringBuilder sb = new StringBuilder("{\"include\":[");
        for (int i = 0; i < slices.size(); i++) {
            long[] s = slices.get(i);
            if (i > 0) sb.append(',');
            sb.append("{\"start\":").append(s[0]).append(",\"end\":").append(s[1]).append('}');
        }
        sb.append("]}");
        System.out.println(sb);
        System.err.printf("Piano: %,d passi  ->  %d job da ~%,d passi%n", total, slices.size(), perJob);
    }

    // ---------------- risultati e checkpoint ----------------

    @SuppressWarnings("unchecked")
    static void reportHit(Object[] h) {
        BigInteger n = (BigInteger) h[3];
        List<BigInteger[]> reps = (List<BigInteger[]>) h[4];
        String verdict = n.compareTo(CURRENT_BEST) < 0 ? "!!! MIGLIORE DEL BOUND NOTO - VERIFICARE CON ESTREMA ATTENZIONE !!!"
            : n.equals(CURRENT_BEST) ? "(coincide con il Ta(7) noto)" : "(maggiore del bound noto)";
        StringBuilder sb = new StringBuilder();
        sb.append("*** seed idx=").append(h[0]).append(" s=").append(h[1]).append(" M=").append(h[2])
          .append(" -> N=").append(n).append("  (").append(reps.size()).append(" rappresentazioni) ").append(verdict).append('\n');
        for (BigInteger[] p : reps) sb.append("    ").append(p[0]).append("^3 + ").append(p[1]).append("^3\n");
        synchronized (System.out) { System.out.print(sb); }
        try {
            Files.writeString(Paths.get(RESULTS_FILE), sb.toString(), StandardCharsets.UTF_8,
                StandardOpenOption.CREATE, StandardOpenOption.APPEND);
        } catch (IOException e) {
            System.out.println("(attenzione: impossibile scrivere " + RESULTS_FILE + ": " + e.getMessage() + ")");
        }
    }

    static Long readCheckpoint(String fingerprint) throws IOException {
        Path p = Paths.get(CHECKPOINT_FILE);
        if (!Files.exists(p)) return null;
        String fp = null; Long next = null;
        for (String line : Files.readAllLines(p, StandardCharsets.UTF_8)) {
            if (line.startsWith("fingerprint=")) fp = line.substring("fingerprint=".length());
            else if (line.startsWith("nextIndex=")) next = Long.parseLong(line.substring("nextIndex=".length()).trim());
        }
        if (fp == null || next == null) throw new IllegalStateException("Checkpoint illeggibile: " + CHECKPOINT_FILE);
        if (!fp.equals(fingerprint)) {
            throw new IllegalStateException("Il checkpoint " + CHECKPOINT_FILE + " appartiene a una famiglia DIVERSA da quella "
                + "configurata (PRIMES / MIN_PRIMES_IN_SEED / S_MIN / S_MAX cambiati?).\n  checkpoint: " + fp
                + "\n  attuale:    " + fingerprint + "\nRipristina i parametri oppure usa un altro CHECKPOINT_FILE.");
        }
        return next;
    }

    static void writeCheckpoint(String fingerprint, long nextIndex, long stepsDone) throws IOException {
        Path p = Paths.get(CHECKPOINT_FILE);
        Path tmp = Paths.get(CHECKPOINT_FILE + ".tmp");
        Files.writeString(tmp, "fingerprint=" + fingerprint + "\nnextIndex=" + nextIndex + "\nstepsDone=" + stepsDone + "\n", StandardCharsets.UTF_8);
        Files.move(tmp, p, StandardCopyOption.REPLACE_EXISTING);
    }

    // ---------------- famiglia di seed ----------------

    /** Sottoinsiemi di PRIMES con >= MIN_PRIMES_IN_SEED primi e S_MIN <= s <= S_MAX; mLimit = cbrt(bound/s). */
    static void genSeeds(int i, long s, int k, long mask, List<long[]> out) {
        if (s > S_MAX) return;
        if (i == PRIMES.length) {
            boolean hasNewPrime = (mask >>> OLD_PRIMES_COUNT) != 0L;
            if (k >= MIN_PRIMES_IN_SEED && k <= MAX_PRIMES_IN_SEED && s >= S_MIN && hasNewPrime) {
                long mLimit = cbrtFloor(CURRENT_BEST.divide(BigInteger.valueOf(s))).longValueExact();
                out.add(new long[]{s, mask, mLimit});
            }
            return;
        }
        genSeeds(i + 1, s, k, mask, out);
        genSeeds(i + 1, s * PRIMES[i], k + 1, mask | (1L << i), out);
    }

    // ---------------- nucleo: test ESATTO per N = M^3 * s ----------------

    /** Tutte le mediane m = mu*d (mu | M^3, d | s) con N = M^3*s = (m-h)^3+(m+h)^3, 0<h<m. Restituisce le coppie (a,b). */
    static List<BigInteger[]> searchRepresentations(long m, BigInteger seedValue, BigInteger[] seedDivisors, int[] spf) {
        BigInteger n = BigInteger.valueOf(m).pow(3).multiply(seedValue);

        // finestra per la mediana cbrt(N/8) < m < cbrt(N/2): calcolata in double e ALLARGATA
        // (e' solo un pre-filtro: la correttezza e' garantita dal test esatto sotto)
        double nd = n.doubleValue();
        BigInteger low = BigInteger.valueOf(Math.max(1L, (long) Math.floor(Math.cbrt(nd / 8.0) * (1 - 1e-9)) - 2));
        BigInteger high = BigInteger.valueOf((long) Math.ceil(Math.cbrt(nd / 2.0) * (1 + 1e-9)) + 2);

        Map<BigInteger, Integer> mCubed = new TreeMap<>();
        for (Map.Entry<BigInteger, Integer> e : factorizeWithSpf(m, spf).entrySet()) mCubed.put(e.getKey(), e.getValue() * 3);
        BigInteger[] muDivisors = divisorsSorted(mCubed);

        List<BigInteger[]> found = new ArrayList<>();
        Set<BigInteger> seen = new HashSet<>();
        for (BigInteger mu : muDivisors) {
            BigInteger dLow = ceilDiv(low, mu);
            BigInteger dHigh = high.divide(mu);
            if (dHigh.compareTo(dLow) < 0) continue;
            int lo = lowerBound(seedDivisors, dLow), hi = upperBound(seedDivisors, dHigh);
            for (int i = lo; i < hi; i++) {
                BigInteger median = mu.multiply(seedDivisors[i]);
                if (!seen.add(median)) continue;
                BigInteger diff = n.subtract(BigInteger.TWO.multiply(median.pow(3)));
                if (diff.signum() <= 0) continue;
                BigInteger[] qr = diff.divideAndRemainder(BigInteger.valueOf(6).multiply(median));
                if (qr[1].signum() != 0) continue;
                BigInteger h = qr[0].sqrt();
                if (h.multiply(h).equals(qr[0]) && h.signum() > 0 && h.compareTo(median) < 0)
                    found.add(new BigInteger[]{median.subtract(h), median.add(h)});
            }
        }
        return found;
    }

    // ---------------- utilita' ----------------

    /** Crivello del piu' piccolo fattore primo fino a limit. */
    static int[] buildSpf(int limit) {
        int[] spf = new int[limit + 1];
        for (int i = 2; i <= limit; i++) {
            if (spf[i] == 0) for (long j = i; j <= limit; j += i) if (spf[(int) j] == 0) spf[(int) j] = i;
        }
        return spf;
    }

    static Map<BigInteger, Integer> factorizeWithSpf(long m, int[] spf) {
        Map<BigInteger, Integer> f = new TreeMap<>();
        while (m > 1) {
            int p = spf[(int) m], c = 0;
            while (m % p == 0) { m /= p; c++; }
            f.put(BigInteger.valueOf(p), c);
        }
        return f;
    }

    static BigInteger[] divisorsSorted(Map<BigInteger, Integer> factors) {
        List<BigInteger> divs = new ArrayList<>();
        divs.add(BigInteger.ONE);
        for (Map.Entry<BigInteger, Integer> e : factors.entrySet()) {
            int size = divs.size();
            List<BigInteger> nd = new ArrayList<>(divs);
            BigInteger pk = BigInteger.ONE;
            for (int k = 1; k <= e.getValue(); k++) {
                pk = pk.multiply(e.getKey());
                for (int i = 0; i < size; i++) nd.add(divs.get(i).multiply(pk));
            }
            divs = nd;
        }
        BigInteger[] arr = divs.toArray(new BigInteger[0]);
        Arrays.sort(arr);
        return arr;
    }

    static BigInteger cbrtFloor(BigInteger n) {
        if (n.signum() <= 0) return BigInteger.ZERO;
        BigInteger lo = BigInteger.ZERO, hi = BigInteger.ONE.shiftLeft(n.bitLength() / 3 + 2);
        while (lo.compareTo(hi) < 0) {
            BigInteger mid = lo.add(hi).add(BigInteger.ONE).shiftRight(1);
            if (mid.pow(3).compareTo(n) <= 0) lo = mid; else hi = mid.subtract(BigInteger.ONE);
        }
        return lo;
    }

    static BigInteger ceilDiv(BigInteger a, BigInteger b) {
        BigInteger[] qr = a.divideAndRemainder(b);
        return qr[1].signum() == 0 ? qr[0] : qr[0].add(BigInteger.ONE);
    }

    static int lowerBound(BigInteger[] arr, BigInteger v) {
        int lo = 0, hi = arr.length;
        while (lo < hi) { int mid = (lo + hi) >>> 1; if (arr[mid].compareTo(v) < 0) lo = mid + 1; else hi = mid; }
        return lo;
    }

    static int upperBound(BigInteger[] arr, BigInteger v) {
        int lo = 0, hi = arr.length;
        while (lo < hi) { int mid = (lo + hi) >>> 1; if (arr[mid].compareTo(v) <= 0) lo = mid + 1; else hi = mid; }
        return lo;
    }
}
