import javafx.util.Pair;

import java.io.IOException;
import java.io.FileReader;
import java.io.FileWriter;
import java.util.*;

public class Sudoku {

    private final int NUM_VARS = 81;
    private int vars[] = new int[NUM_VARS];
    private boolean varDomain[][] = new boolean[NUM_VARS][9];
    private int varsI[] = new int[NUM_VARS];
    private boolean varDomainI[][] = new boolean[NUM_VARS][9];
    private int guess_count = 0;

    public static void main(String[] args) {
        int []fileNumbers = new int[]{1,2,10,15,25,26,48,51,62,76,81,82,90,95,99,100};
        for(int fileNumber:fileNumbers){
            String fileName = "src/input"+fileNumber+".txt";
            Sudoku solver = new Sudoku();
            solver.makeSudokuPuzzle(fileName);
            //solver.printSudoku();
            //boolean result = solver.simpleBackTracking();
           // boolean result = solver.MRVBackTracking();
            boolean result = solver.MRVBackTrackingWithInference();
            if (result) {
                System.out.println("Sudoku "+fileNumber+" : Guesses : "+solver.guess_count);
            } else {
                System.out.println("Failure!");
            }
            //solver.printSudoku();
        }





    }

    /****************************************************************************************************/
    // Sudoku solver with MRV Heuristic with Inferences
    public boolean MRVBackTrackingWithInference() {
        if (isComplete()) {
            return true;
        }

        int var = -1;
        int remValues[] = getRemainingValues();
        int minValue = Integer.MAX_VALUE;
        for (int i = 0; i < NUM_VARS; i++) {
            if (vars[i] == 0) {
                if (remValues[i] < minValue) {
                    minValue = remValues[i];
                    var = i;
                }
            }
        }
        if (var == -1) {
            return false;
        }

        List<Integer> domainValues = getDomainValues(var);
        if (minValue < domainValues.size()) {
            guess_count = guess_count + minValue - 1;
        } else {
            guess_count = guess_count + domainValues.size() - 1;
        }

        for (int val : domainValues) {

            int[] varsBackup = takeVarsBackup();
            boolean varDomainBackup[][] = takeDomainsBackup();

            vars[var] = val + 1;
            assignValue(var, val);
            if (isConsistent()) {
                if (waterfall()) {
                    restoreBackup();
                    boolean result = MRVBackTrackingWithInference();
                    if (result) {
                        return true;
                    }
                }
            }
            copyBackVars(varsBackup);
            copyBackDomain(varDomainBackup);
        }
        return false;
    }

    //Waterfall of inference methods
    public boolean waterfall() {
        takeStateBackup();
        boolean ac3result = ac3();
        if(ac3result){
            nakedPairs();
        }
        return ac3result;
    }


    // AC-3 Inference function
    public boolean ac3() {
        Queue<Pair<Integer, Integer>> arcQueue = new ArrayDeque<Pair<Integer, Integer>>();
        Set<Pair<Integer, Integer>> arcs = new HashSet<Pair<Integer, Integer>>();
        for (int i = 0; i < NUM_VARS; i++) {
            if (varsI[i] == 0) {
                List<Pair<Integer, Integer>> neighbours = getNeighbours(i, -1);
                arcs.addAll(neighbours);
            }
        }
        for (Pair<Integer, Integer> arc : arcs) {
            arcQueue.offer(arc);
        }

        while (!arcQueue.isEmpty()) {
            Pair<Integer, Integer> arc = arcQueue.poll();
            if (revise(arc)) {
                if (isDomainZero(arc.getKey())) {
                    return false;
                }
                List<Pair<Integer, Integer>> neighbours = getNeighbours(arc.getKey(), arc.getValue());
                arcs.addAll(neighbours);
            }
        }

        return true;
    }

    //AC3 Revision Function
    public boolean revise(Pair<Integer, Integer> arc) {
        boolean revised = false;
        int x = arc.getKey();
        int y = arc.getValue();

        for (int i = 0; i < 9; i++) {
            boolean valid = false;
            if (varDomainI[x][i]) {
                for (int j = 0; j < 9; j++) {
                    if (varDomainI[y][j]) {
                        if (i != j) {
                            valid = true;
                        }
                    }
                }
            }
            if (!valid) {
                varDomainI[x][i] = false;
                revised = true;
            }

        }

        return revised;
    }

    //Naked Pair Inference Function
    public void nakedPairs() {
        for (int i = 0; i < NUM_VARS; i++) {
            if (varsI[i] == 0) {
                List<Integer> domain = new ArrayList<>();

                for (int j = 0; j < 9; j++) {
                    if (varDomainI[i][j]) {
                        domain.add(j);
                    }
                }

                if (domain.size() != 2) {
                    continue;
                }

                //Checking for rows
                List<Integer> rowNeigh = new ArrayList<>();
                List<Pair<Integer, Integer>> rowNneighbours = getRowNeighbours(i, -1);

                for (Pair<Integer, Integer> pair : rowNneighbours) {
                    if (varsI[pair.getValue()] == 0) {
                        rowNeigh.add(pair.getValue());
                    }

                }
                int flag = -1;
                for (Integer neighbour : rowNeigh) {
                    List<Integer> NDomain = new ArrayList<>();
                    for (int j = 0; j < 9; j++) {
                        if (varDomainI[neighbour][j]) {
                            NDomain.add(j);
                        }
                    }
                    if (NDomain.size() == 2 && domain.get(0) == NDomain.get(0) && domain.get(1) == NDomain.get(1)) {
                        flag = neighbour;
                        break;
                    }
                }

                if (flag != -1) {
                    for (Integer neighbour : rowNeigh) {
                        if (neighbour == i || neighbour == flag || varsI[neighbour] != 0) {
                            continue;
                        }
                        varDomainI[neighbour][domain.get(0)] = false;
                        varDomainI[neighbour][domain.get(1)] = false;
                    }
                }

                //Checking for columns
                List<Integer> colNeigh = new ArrayList<>();
                List<Pair<Integer, Integer>> colNneighbours = getColumnNeighbours(i, -1);

                for (Pair<Integer, Integer> pair : colNneighbours) {
                    if (varsI[pair.getValue()] == 0) {
                        colNeigh.add(pair.getValue());
                    }

                }
                flag = -1;
                for (Integer neighbour : colNeigh) {
                    List<Integer> NDomain = new ArrayList<>();
                    for (int j = 0; j < 9; j++) {
                        if (varDomainI[neighbour][j]) {
                            NDomain.add(j);
                        }
                    }
                    if (NDomain.size() == 2 && domain.get(0) == NDomain.get(0) && domain.get(1) == NDomain.get(1)) {
                        flag = neighbour;
                        break;
                    }
                }

                if (flag != -1) {
                    for (Integer neighbour : colNeigh) {
                        if (neighbour == i || neighbour == flag || varsI[neighbour] != 0) {
                            continue;
                        }
                        varDomainI[neighbour][domain.get(0)] = false;
                        varDomainI[neighbour][domain.get(1)] = false;
                    }
                }

                //Checking for boxes
                List<Integer> boxNeigh = new ArrayList<>();
                List<Pair<Integer, Integer>> boxNneighbours = getBoxNeighbours(i, -1);

                for (Pair<Integer, Integer> pair : boxNneighbours) {
                    if (varsI[pair.getValue()] == 0) {
                        boxNeigh.add(pair.getValue());
                    }

                }
                flag = -1;
                for (Integer neighbour : boxNeigh) {
                    List<Integer> NDomain = new ArrayList<>();
                    for (int j = 0; j < 9; j++) {
                        if (varDomainI[neighbour][j]) {
                            NDomain.add(j);
                        }
                    }
                    if (NDomain.size() == 2 && domain.get(0) == NDomain.get(0) && domain.get(1) == NDomain.get(1)) {
                        flag = neighbour;
                        break;
                    }
                }

                if (flag != -1) {
                    for (Integer neighbour : boxNeigh) {
                        if (neighbour == i || neighbour == flag || varsI[neighbour] != 0) {
                            continue;
                        }
                        varDomainI[neighbour][domain.get(0)] = false;
                        varDomainI[neighbour][domain.get(1)] = false;
                    }
                }

            }
        }
    }

    //AC-3 Helper Functions
    public List<Pair<Integer, Integer>> getNeighbours(int var, int excluded) {
        List<Pair<Integer, Integer>> neighbours = new ArrayList<Pair<Integer, Integer>>();
        int row = var / 9;
        int col = var % 9;

        for (int c = 0; c < 9; c++) {
            int pos = row * 9 + c;
            if (pos != var && pos != excluded) {
                Pair<Integer, Integer> p = new Pair<>(var, pos);
                neighbours.add(p);
            }
        }

        for (int r = 0; r < 9; r++) {
            int pos = r * 9 + col;
            if (pos != var && pos != excluded) {
                Pair<Integer, Integer> p = new Pair<>(var, pos);
                neighbours.add(p);
            }
        }

        int box_col = col / 3;
        int box_row = row / 3;
        int cornerPos = (3 * box_row * 9) + (3 * box_col);

        for (int i = 0; i < 3; i++) {
            for (int j = 0; j < 27; j = j + 9) {
                int pos = cornerPos + i + j;
                if (pos != var && pos != excluded) {
                    Pair<Integer, Integer> p = new Pair<>(var, pos);
                    neighbours.add(p);
                }
            }
        }
        return neighbours;

    }

    public List<Pair<Integer, Integer>> getBoxNeighbours(int var, int excluded) {
        List<Pair<Integer, Integer>> neighbours = new ArrayList<Pair<Integer, Integer>>();
        int row = var / 9;
        int col = var % 9;

        int box_col = col / 3;
        int box_row = row / 3;
        int cornerPos = (3 * box_row * 9) + (3 * box_col);

        for (int i = 0; i < 3; i++) {
            for (int j = 0; j < 27; j = j + 9) {
                int pos = cornerPos + i + j;
                if (pos != var && pos != excluded) {
                    Pair<Integer, Integer> p = new Pair<>(var, pos);
                    neighbours.add(p);
                }
            }
        }
        return neighbours;

    }

    public List<Pair<Integer, Integer>> getRowNeighbours(int var, int excluded) {
        List<Pair<Integer, Integer>> neighbours = new ArrayList<Pair<Integer, Integer>>();
        int row = var / 9;
        int col = var % 9;

        for (int r = 0; r < 9; r++) {
            int pos = r * 9 + col;
            if (pos != var && pos != excluded) {
                Pair<Integer, Integer> p = new Pair<>(var, pos);
                neighbours.add(p);
            }
        }


        return neighbours;

    }

    public List<Pair<Integer, Integer>> getColumnNeighbours(int var, int excluded) {
        List<Pair<Integer, Integer>> neighbours = new ArrayList<Pair<Integer, Integer>>();
        int row = var / 9;
        int col = var % 9;

        for (int c = 0; c < 9; c++) {
            int pos = row * 9 + c;
            if (pos != var && pos != excluded) {
                Pair<Integer, Integer> p = new Pair<>(var, pos);
                neighbours.add(p);
            }
        }

        return neighbours;

    }

    public boolean isDomainZero(int var) {
        for (int i = 0; i < 9; i++) {
            if (varDomainI[var][i]) {
                return false;
            }
        }
        return true;
    }


    /**************************************************************************************************/


    // simple Backtracking Sudoku solver
    public boolean simpleBackTracking() {
        if (isComplete()) {
            return true;
        }

        int var = -1;
        for (int i = 0; i < NUM_VARS; i++) {
            if (vars[i] == 0) {
                var = i;
                break;
            }
        }

        if (var == -1) {
            return false;
        }

        guess_count = guess_count + 8;

        for (int val = 0; val < 9; val++) {

            int[] varsBackup = takeVarsBackup();
            boolean varDomainBackup[][] = takeDomainsBackup();

            vars[var] = val + 1;
            assignValue(var, val);
            if (isConsistent()) {
                boolean result = simpleBackTracking();
                if (result) {
                    return true;
                }
            }
            copyBackVars(varsBackup);
            copyBackDomain(varDomainBackup);

        }
        return false;
    }

    /**************************************************************************************************/

    // Sudoku solver with MRV Heuristic
    public boolean MRVBackTracking() {
        if (isComplete()) {
            return true;
        }

        int var = -1;
        int remValues[] = getRemainingValues();
        int minValue = Integer.MAX_VALUE;
        for (int i = 0; i < NUM_VARS; i++) {
            if (vars[i] == 0) {
                if (remValues[i] < minValue) {
                    minValue = remValues[i];
                    var = i;
                }
            }
        }
        if (var == -1) {
            return false;
        }
        guess_count = guess_count + 8;
        for (int val = 0; val < 9; val++) {

            int[] varsBackup = takeVarsBackup();
            boolean varDomainBackup[][] = takeDomainsBackup();

            vars[var] = val + 1;
            assignValue(var, val);
            if (isConsistent()) {
                boolean result = MRVBackTracking();
                if (result) {
                    return true;
                }
            }
            copyBackVars(varsBackup);
            copyBackDomain(varDomainBackup);
        }

        return false;
    }


    //MRV Helper Functions
    public int[] getRemainingValues() {
        int result[] = new int[NUM_VARS];
        for (int i = 0; i < NUM_VARS; i++) {
            if (vars[i] == 0) {
                int remainingValue = getRemainingValue(i);
                result[i] = remainingValue;
            } else {
                result[i] = -1;
            }
        }
        return result;
    }

    public int getRemainingValue(int var) {
        Map<Integer, Integer> occupiedPoss = new HashMap<>();
        int row = var / 9;
        int col = var % 9;

        for (int c = 0; c < 9; c++) {
            int pos = row * 9 + c;
            if (vars[pos] == 0) {
                continue;
            }
            for (int i = 0; i < 9; i++) {
                if (varDomain[pos][i]) {
                    occupiedPoss.put(i, occupiedPoss.getOrDefault(i, 0));
                    break;
                }
            }
        }

        for (int r = 0; r < 9; r++) {
            int pos = r * 9 + col;
            if (vars[pos] == 0) {
                continue;
            }
            for (int i = 0; i < 9; i++) {
                if (varDomain[pos][i]) {
                    occupiedPoss.put(i, occupiedPoss.getOrDefault(i, 0));
                    break;
                }
            }
        }

        int box_col = col / 3;
        int box_row = row / 3;
        int cornerPos = (3 * box_row * 9) + (3 * box_col);
        for (int i = 0; i < 3; i++) {
            for (int j = 0; j < 27; j = j + 9) {
                int pos = cornerPos + i + j;
                if (vars[pos] == 0) {
                    continue;
                }
                for (int k = 0; k < 9; k++) {
                    if (varDomain[pos][k]) {
                        occupiedPoss.put(k, occupiedPoss.getOrDefault(k, 0));
                        break;
                    }
                }
            }
        }

        return (9 - occupiedPoss.keySet().size());
    }

    /**************************************************************************************************/

    //Sudoku Solver Helper Functions
    public boolean isComplete() {
        for (int i = 0; i < NUM_VARS; i++) {
            if (vars[i] == 0) {
                return false;
            }
        }
        return true;
    }

    public List<Integer> getDomainValues(int var) {
        List<Integer> vals = new ArrayList<>();
        for (int i = 0; i < 9; i++) {
            if (varDomain[var][i]) {
                vals.add(i);
            }
        }
        return vals;
    }


    //checks if solution is consistent by checking the constraints
    public boolean isConsistent() {
        return checkRowConstraint() && checkColumnConstraint() && checkBoxConstraint();
    }


    //Checks row constraint
    public boolean checkRowConstraint() {
        Map<Integer, Boolean> constraint = new HashMap<>();
        for (int i = 0; i < 9; i++) {
            constraint.clear();
            for (int j = 9 * i; j < 9 * (i + 1); j++) {
                if (vars[j] == 0) {
                    continue;
                }
                for (int k = 0; k < 9; k++) {
                    if (varDomain[j][k]) {
                        if (!constraint.containsKey(k)) {
                            constraint.put(k, true);
                        } else {
                            return false;
                        }
                    }
                }
            }
        }
        return true;
    }


    //Checks column constraint
    public boolean checkColumnConstraint() {
        Map<Integer, Boolean> constraint = new HashMap<>();
        for (int i = 0; i < 9; i++) {
            constraint.clear();
            for (int j = i; j < 73 + i; j = j + 9) {
                if (vars[j] == 0) {
                    continue;
                }
                for (int k = 0; k < 9; k++) {
                    if (varDomain[j][k]) {
                        if (!constraint.containsKey(k)) {
                            constraint.put(k, true);
                        } else {
                            return false;
                        }
                    }
                }
            }
        }
        return true;
    }


    //Checks box constraint
    public boolean checkBoxConstraint() {
        Map<Integer, Boolean> constraint = new HashMap<>();
        for (int n = 0; n < 55; n = n + 27) {
            for (int m = 0; m < 7; m = m + 3) {
                constraint.clear();
                for (int i = 0; i < 19; i = i + 9) {
                    for (int j = 0; j < 3; j++) {
                        if (vars[j + i + m + n] == 0) {
                            continue;
                        }
                        for (int k = 0; k < 9; k++) {
                            if (varDomain[j + i + m + n][k]) {
                                if (!constraint.containsKey(k)) {
                                    constraint.put(k, true);
                                } else {
                                    return false;
                                }
                            }
                        }
                    }
                }
            }
        }

        return true;
    }

    public void assignValue(int var, int val) {
        for (int i = 0; i < 9; i++) {
            if (i != val) {
                varDomain[var][i] = false;
            }
        }
    }

    public void resetDomain(int var) {
        for (int i = 0; i < 9; i++) {
            varDomain[var][i] = true;

        }
    }

    /**************************************************************************************************/

    //reads a sudoku from input file
    public void makeSudokuPuzzle(String fileName) {
        try {
            FileReader file = new FileReader(fileName);
            for (int a = 0; a < NUM_VARS; a++) {
                char ch;
                do {
                    ch = (char) file.read();
                } while ((ch == '\n') || (ch == '\r') || (ch == ' '));
                if (ch == '-') {
                    vars[a] = 0;
                    for (int i = 0; i < 9; i++) {
                        varDomain[a][i] = true;
                    }
                } else {
                    String s = "" + ch;
                    Integer i = new Integer(s);
                    vars[a] = i.intValue();
                    for (int j = 0; j < 9; j++) {
                        if (j == i.intValue() - 1)
                            varDomain[a][j] = true;
                        else
                            varDomain[a][j] = false;
                    }
                }
            }

            file.close();
        } catch (IOException e) {
            System.out.println("File read error: " + e);
        }
    }


    //writes a Sudoku to output file
    public void printSudoku() {
        try {
            FileWriter ofile = new FileWriter("output.txt", true);
            for (int a = 0; a < 9; a++) {
                for (int b = 0; b < 9; b++) {
                    int c = 9 * a + b;
                    if (vars[c] == 0) {
                        System.out.print("- ");
                        ofile.write("- ");
                    } else {
                        System.out.print(vars[c] + " ");
                        ofile.write(vars[c] + " ");
                    }
                }
                System.out.println("");
                ofile.write("\r\n");
            }
            ofile.write("\r\n");
            ofile.close();
        } catch (IOException e) {
            System.out.println("File read error: " + e);
        }
    }

    /**************************************************************************************************/

    public void takeStateBackup() {
        for (int i = 0; i < NUM_VARS; i++) {
            varsI[i] = vars[i];
            for (int j = 0; j < 9; j++) {
                varDomainI[i][j] = varDomain[i][j];
            }
        }
    }

    public void restoreBackup() {
        for (int i = 0; i < NUM_VARS; i++) {
            for (int j = 0; j < 9; j++) {
                varDomain[i][j] = varDomainI[i][j];
            }
        }
    }


    public int[] takeVarsBackup() {
        int[] b = new int[NUM_VARS];
        for (int i = 0; i < NUM_VARS; i++) {
            b[i] = vars[i];
        }
        return b;
    }

    public boolean[][] takeDomainsBackup() {
        boolean b[][] = new boolean[NUM_VARS][9];
        for (int i = 0; i < NUM_VARS; i++) {
            for (int j = 0; j < 9; j++) {
                b[i][j] = varDomain[i][j];
            }
        }
        return b;
    }

    public void copyBackVars(int[] b) {
        for (int i = 0; i < NUM_VARS; i++) {
            vars[i] = b[i];
        }
    }

    public void copyBackDomain(boolean[][] b) {
        for (int i = 0; i < NUM_VARS; i++) {
            for (int j = 0; j < 9; j++) {
                varDomain[i][j] = b[i][j];
            }
        }
    }

}
