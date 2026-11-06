package edu.mit.csail.sdg.translator;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Sig;
import java.io.BufferedWriter;
import java.io.FileWriter;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;
import kodkod.engine.Solver;
import kodkod.engine.satlab.MaxSATSolver;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.SATSolver;

/** Solver adapter for the pinned AlloyMax 1.0.2 API; the JAR is not modified. */
public final class Z3Bridge {
    public interface Callback {
        // Positive variable IDs in an optimal model; null means UNSAT.
        int[] solve(String path, int variables);
    }

    private static final class Factory extends SATFactory {
        private final Callback callback;
        private final String path;
        Factory(Callback callback, String path) { this.callback = callback; this.path = path; }
        public SATSolver instance() { return new Backend(callback, path); }
        public boolean incremental() { return false; }
    }

    private static final class Backend implements MaxSATSolver {
        private final Callback callback;
        private final String path;
        private final List<Clause> cached = new ArrayList<>();
        private int variables, clauses, priority;
        private Boolean sat;
        private BitSet model;
        Backend(Callback callback, String path) { this.callback = callback; this.path = path; }
        public int numberOfVariables() { return variables; }
        public int numberOfClauses() { return clauses; }
        public void addVariables(int count) {
            if (count < 0) throw new IllegalArgumentException("Negative variable count");
            variables += count;
        }
        public Boolean isSAT() { return sat; }
        public void incNumberOfClauses() { clauses++; }
        public List<Clause> getCached() { return cached; }
        public int getMaxPriority() { return priority; }
        public void setMaxPriority(int value) { priority = Math.max(priority, value); }
        public boolean actualSolve(int[] weights) {
            long top = 1;
            for (Clause clause : cached) if (clause.isSoft()) top += weights[clause.getPriority()];
            try (BufferedWriter out = new BufferedWriter(new FileWriter(path))) {
                out.write("p wcnf " + variables + " " + cached.size() + " " + top + "\n");
                for (Clause clause : cached) {
                    out.write(Long.toString(clause.isSoft() ? weights[clause.getPriority()] : top));
                    for (int literal : clause.getLits()) { out.write(' '); out.write(Integer.toString(literal)); }
                    out.write(" 0\n");
                }
            } catch (Exception exception) { throw new RuntimeException(exception); }
            int[] truth = callback.solve(path, variables);
            sat = truth != null;
            if (sat) {
                model = new BitSet(variables + 1);
                for (int variable : truth) {
                    if (variable < 1 || variable > variables) throw new IllegalStateException("Invalid Z3 assignment");
                    model.set(variable);
                }
                for (Clause clause : cached) {
                    boolean satisfied = false;
                    for (int literal : clause.getLits())
                        if (model.get(Math.abs(literal)) == (literal > 0)) { satisfied = true; break; }
                    if (!clause.isSoft() && !satisfied)
                        throw new IllegalStateException("Z3 assignment violates an exported hard clause");
                }
            }
            return sat;
        }
        public boolean valueOf(int variable) {
            if (!Boolean.TRUE.equals(sat) || variable < 1 || variable > variables)
                throw new IllegalStateException("No model value for variable " + variable);
            return model.get(variable);
        }
        public void free() { cached.clear(); }
    }

    public static A4Solution execute(Iterable<Sig> sigs, Command command, A4Options options,
                                     Callback callback, String path) throws Exception {
        if (command.parent != null || !command.getGrowableSigs().isEmpty())
            throw new IllegalArgumentException("Z3 adapter requires a fixed-scope command");
        try {
            Constructor<TranslateAlloyToKodkod> constructor = TranslateAlloyToKodkod.class.getDeclaredConstructor(
                A4Reporter.class, A4Options.class, Iterable.class, Command.class);
            constructor.setAccessible(true);
            TranslateAlloyToKodkod translator = constructor.newInstance(A4Reporter.NOP, options, sigs, command);
            Field frameField = TranslateAlloyToKodkod.class.getDeclaredField("frame");
            frameField.setAccessible(true);
            A4Solution frame = (A4Solution) frameField.get(translator);
            Field solverField = A4Solution.class.getDeclaredField("solver");
            solverField.setAccessible(true);
            ((Solver) solverField.get(frame)).options().setSolver(new Factory(callback, path));
            Method facts = TranslateAlloyToKodkod.class.getDeclaredMethod("makeFacts", Expr.class);
            facts.setAccessible(true);
            facts.invoke(translator, command.formula);
            Class<?> simplifierClass = Class.forName("edu.mit.csail.sdg.translator.Simplifier");
            Constructor<?> simplify = simplifierClass.getDeclaredConstructor();
            simplify.setAccessible(true);
            Method solve = A4Solution.class.getDeclaredMethod("solve", A4Reporter.class, Command.class,
                                                            simplifierClass, boolean.class);
            solve.setAccessible(true);
            return (A4Solution) solve.invoke(frame, A4Reporter.NOP, command, simplify.newInstance(), false);
        } catch (InvocationTargetException exception) {
            Throwable cause = exception.getCause();
            if (cause instanceof Exception) throw (Exception) cause;
            throw new RuntimeException(cause);
        }
    }
}
