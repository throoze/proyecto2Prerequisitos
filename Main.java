import java.io.IOException;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.PrintStream;
import java.util.Iterator;
/**
 *
 * @author victor
 */
public class Main {

    private static DiGraph minimo (DiGraph grafo) {
        if (grafo.numNodes < grafo.numArcs) {
            System.out.print("\nEl grafo original es:\n");
        System.out.println(grafo.toString()+"\n\n");
            DiGraph ret = null;

            ret = (DiGraphMatrix) grafo.clone();
            System.out.print("\nEl grafo clonado es:\n");
        System.out.println(ret.toString()+"\n\n");
            ret = ret.alcance();
            System.out.print("\nEl grafo maximo es:\n");
        System.out.println(ret.toString()+"\n\n");

            // Se agrega la identidad
            for( int i = 0; i < ret.numNodes; ++i ) {
                ret.delArc(i, i);
            }

            for( int k = 0; k < ret.numNodes; ++k ) {
                for( int i = 0; i < ret.numNodes; ++i ) {
                    if( (i != k) && ret.isArc(i,k) ) {
                        for( int j = 0; j < ret.numNodes; ++j ) {
                            if( ret.isArc(k,j) ) {
                                ret.delArc(i, j);
                            }
                        }
                    }
                }
            }

            System.out.print("\nEl grafo minimo es:\n");
        System.out.println(ret.toString()+"\n\n");
            return ret;
        } else {
            return new DiGraphMatrix();
        }
    }

    private static int readFirstLine (String line)
                                        throws ExcepcionFormatoIncorrecto
    {
        String[] tokens = line.split(" ");
        if (tokens.length == 1) {
            if (tokens[0].matches("[0-9]+?")) {
                int numNodos = new Integer(tokens[0]).intValue();
                return numNodos;
            } else {
                throw new ExcepcionFormatoIncorrecto("En la primera linea" +
                        " hay un error de sintaxis: Se esperaba un numero" +
                        " (numCursos) y se encontro: " + tokens[0] + "\n");
            }
        } else {
            throw new ExcepcionFormatoIncorrecto("En la primera linea hay" +
                    "un error de sintaxis: Se esperaban un elemento (" +
                    "numCursos), y se encontro:\n\t" + line);
        }
    }

    private static String[] readNames (BufferedReader inBuff,
                                       String         fileName,
                                       int            numNodes)
            throws ExcepcionArchivoNoSePuedeLeer,
                   ExcepcionFormatoIncorrecto,
                   ExcepcionInconsistenciaNumeroDeNodos,
                   ExcepcionInconsistenciaNumeroDeArcos
    {
        String[] tokens;
        String[] nombres = new String[numNodes];
        String linea = "";
        int k = 2;
        int c = 0;
        try {
            linea = inBuff.readLine();
        } catch (IOException ioe) {
            System.out.println("Esto no deberia pasar, contacte"
                    + " al programador...");
            System.out.println("MENSAJE:" + ioe.getMessage() + "\n"
                    + "CAUSA:" + ioe.getCause().toString() + "\n");
            throw new ExcepcionArchivoNoSePuedeLeer("\nProblema Leyendo la"
                        + "linea " + k + " del archivo \"" + fileName
                        + "\"");
        }
        while (linea != null) {
            if (0 < c && c < numNodes) {
                tokens = linea.split(" ");
                if (tokens.length == 1) {
                    if (tokens[0].matches("[[[0-9[-]][a-z]][A-Z]]+?")) {
                        nombres[c] = tokens[0];
                    } else {
                        throw new ExcepcionFormatoIncorrecto("\nEn la linea "
                          + k + " del archivo \"" + fileName + "\""
                          + " hay un error de sintaxis:\nSe esperaba un numero"
                          + " seguido de otro numero (src dst) y se encontró"
                          + ": \n\t\"" + tokens[0] + " " + tokens[1] + "\"\n");
                    }
                } else {
                    throw new ExcepcionFormatoIncorrecto("\nEn la linea " + k
                      + " del archivo \"" + fileName + "\" hay"
                      + " un error de sintaxis:\nSe esperaban dos elementos"
                      + " (src dst), y se encontro:\n\t\"" + linea + "\"\n");
                }
                k++;
                c++;
                try {
                    linea = inBuff.readLine();
                } catch (IOException ioe) {
                    System.out.println("Esto no deberia pasar, contacte"
                            + " al programador...");
                    System.out.println("MENSAJE:" + ioe.getMessage() + "\n"
                            + "CAUSA:" + ioe.getCause().toString() + "\n");
                    throw new ExcepcionArchivoNoSePuedeLeer("\nProblema " +
                            "Leyendo la linea " + k + " del archivo \"" +
                            fileName + "\"");
                }
            } else {
                throw new ExcepcionInconsistenciaNumeroDeNodos("\nEl " +
                        "grafo de entrada tiene un numero de nodos distinto " +
                        "al indicado al principio del archivo:\nEncontrados " +
                        "\"" + c + "\" cursos (el "+c+"to está en la linea " +
                        k + "), y se esperaban" + numNodes + " cursos...");
            }
        }
        if (linea == null && k-2 != numNodes) {
            throw new ExcepcionInconsistenciaNumeroDeArcos("El grafo de entra" +
                    "da tiene menos arcos que los indicados al principio del " +
                    "archivo:\nTiene " + (k-2) + " arco(s), y se esperaba(n) " +
                    numNodes + " arco(s)");
        }
        return nombres;
    }

    private static int readNumConPrereq (BufferedReader   inBuff,
                                               String           fileName,
                                               int              numLine)
                                        throws ExcepcionFormatoIncorrecto,
                                               ExcepcionArchivoNoSePuedeLeer
    {
        String line = null;
        try {
            line = inBuff.readLine();
        } catch (IOException ioe) {
            System.out.println("Esto no deberia pasar, contacte"
                    + " al programador...");
            System.out.println("MENSAJE:" + ioe.getMessage() + "\n"
                    + "CAUSA:" + ioe.getCause().toString() + "\n");
            throw new ExcepcionArchivoNoSePuedeLeer("\nProblema Leyendo la"
                        + "linea " + numLine + " del archivo \"" + fileName
                        + "\"");
        }
        String[] tokens = line.split(" ");
        if (tokens.length == 1) {
            if (tokens[0].matches("[0-9]+?")) {
                int numCursosConPrereq = new Integer(tokens[0]).intValue();
                return numCursosConPrereq;
            } else {
                throw new ExcepcionFormatoIncorrecto("En la primera linea" +
                        " hay un error de sintaxis: Se esperaba un numero" +
                        " (numCursosConPrerequisito) y se encontro: " +
                        tokens[0] + "\n");
            }
        } else {
            throw new ExcepcionFormatoIncorrecto("En la primera linea hay" +
                    "un error de sintaxis: Se esperaban un elemento (" +
                    "numCursosConPrerequisito), y se encontro:\n\t" + line);
        }
    }

    private static DiGraph read(String fileName)
                                 throws 
                                        FileNotFoundException,
                                        ExcepcionArchivoNoSePuedeLeer,
                                        ExcepcionArchivoNoExiste,
                                        ExcepcionNoEsArchivo,
                                        ExcepcionFormatoIncorrecto,
                                        ExcepcionInconsistenciaNumeroDeNodos,
                                        ExcepcionInconsistenciaNumeroDeArcos
    {
        if ((new File(fileName)).exists() &&
            (new File(fileName)).isFile() &&
            (new File(fileName)).canRead())  {
            BufferedReader inBuff = null;
            try {
                inBuff = new BufferedReader(new FileReader(fileName));
            } catch (FileNotFoundException fnfe) {
                System.out.println("Esto no deberia pasar, contacte" +
                        " al programador...");
                System.out.println("MENSAJE:" + fnfe.getMessage() + "\n" +
                        "CAUSA:" + fnfe.getCause().toString() + "\n");
                throw new ExcepcionArchivoNoSePuedeLeer("Problema Leyendo el" +
                        " archivo \"" + fileName +
                        "\" al momento de crear el buffer lector...\n");
            }
            String linea = null;
            try {
                 linea = inBuff.readLine();
            } catch (IOException ioe) {
                System.out.println("Esto no deberia pasar, contacte" +
                        " al programador...");
                System.out.println("MENSAJE:" + ioe.getMessage() + "\n" +
                        "CAUSA:" + ioe.getCause().toString() + "\n");
                throw new ExcepcionArchivoNoSePuedeLeer("Problema Leyendo la" +
                        "primera linea del archivo \"" + fileName +
                        "\"");
            }
            int numNodes = readFirstLine(linea);
            String[] nombres = readNames(inBuff,fileName,numNodes);
            int numLinea = nombres.length + 2;
            int numCurConPrereq = readNumConPrereq(inBuff,fileName,numLinea);
            List<Arc> arcos = new Lista();

            DiGraph digrafo = null;
            if (numNodes <= arcos.size()) {
                digrafo = new DiGraphList();
            } else {
                digrafo = new DiGraphMatrix();
            }
            Iterator iterador = arcos.iterator();
            while (iterador.hasNext()) {
                Arc actual = (Arc)iterador.next();
                digrafo.addArc(actual);
            }
            digrafo.setNames(nombres);
            return digrafo;
        } else if (!(new File(fileName)).exists()) {
            throw new ExcepcionArchivoNoExiste("Problema al leer el archivo " +
                    "\"" + fileName +"\": EL ARCHIVO NO EXISTE!!!");
        } else if (!(new File(fileName)).isFile()) {
            throw new ExcepcionNoEsArchivo("Problema al leer el archivo \"" +
                    fileName +"\": NO ES UN ARCHIVO!!!");
        } else if (!(new File(fileName)).canRead()) {
            throw new ExcepcionArchivoNoSePuedeLeer("Problema al leer el ar" +
                    "chivo \"" + fileName +"\": ESTE ARCHIVO NO SE PUEDE" +
                    " LEER!!!");
        }
        return null;
    }

    public static void write(String fileName) throws IOException {

    }



    /**
     * @param args the command line arguments
     */
    public static void main(String[] args) throws IOException {
        DiGraph digrafo = new DiGraphMatrix(args[0]);
        DiGraph result = minimo(digrafo);
        System.out.print("\nEl grafo minimo es:\n");
        System.out.println(result.toString()+"\n\n");
        //result.write(args[1]);
        String[] arreglo = {"q","w","e","r","t","y","u","i","o","p","a","s","d","f","g","h","j","k","l","z","x","c","v","b","n","m"};
        System.out.print("\nEl arreglo desordenado es:\n");
        System.out.print("\t[ ");
        for (int k = 0; k < arreglo.length - 1; k++) {
            System.out.print(arreglo[k] + ", ");
        }
        System.out.print(arreglo[arreglo.length-1] + " ]\n\n");
        Ordenar.mergesortString(arreglo);
        System.out.print("\nEl arreglo ordenado es:\n");
        System.out.print("\t[ ");
        for (int k = 0; k < arreglo.length - 1; k++) {
            System.out.print(arreglo[k] + ", ");
        }
        System.out.print(arreglo[arreglo.length-1] + " ]\n\n");
        
    }
}
