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
    
    private String[] nameNodes;
    private int numNodes;

    private static String getName(int n, String[] nombres) {
        if (0 <= n && n < nombres.length) {
            return nombres[n];
        } else {
            return "";
        }
    }

    private static int getNumber(String name, String[] nombres) {
        int posicion = Buscar.bb(nombres, name);
        if (0 <= posicion && posicion < nombres.length &&
                nombres[posicion].equals(name)) {
            return posicion;
        } else {
            return -1;
        }
    }

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

    private static boolean pertenece(String elem, String[] arr) {
        boolean pertenece = false;
        int pos = Buscar.bb(arr, elem);
        if (0 <= pos && pos < arr.length && arr[pos].equals(elem)) {
            pertenece = true;
        }
        return pertenece;
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
            throw new ExcepcionArchivoNoSePuedeLeer("Esto no debería pasar, " +
                    "contacte al programador...\nProblema Leyendo la linea " +
                    k + " del archivo \"" + fileName + "\"");
        }
        while (0 <= c && c < numNodes && linea != null) {
            tokens = linea.split(" ");
            if (tokens.length == 1) {
                if (tokens[0].matches("[[[0-9[-]][a-z]][A-Z]]+?")) {
                    nombres[c] = tokens[0];
                } else {
                    throw new ExcepcionFormatoIncorrecto("\nEn la linea "
                      + k + " del archivo \"" + fileName + "\" hay un error" +
                      " de sintaxis:\nSe esperaba el nombre de un curso y se" +
                      " encontró: \n\t\"" + tokens[0] + "\"\n");
                }
            } else {
                throw new ExcepcionFormatoIncorrecto("\nEn la linea " + k
                  + " del archivo \"" + fileName + "\" hay un error de " +
                  "sintaxis:\nSe esperaba sólo un elemento (nombreCurso), y " +
                  "se encontro:\n\t\"" + linea + "\"\n");
            }
            k++;
            c++;
            try {
                if (c == numNodes) {
                    inBuff.mark(99999);
                }
                linea = inBuff.readLine();
                if (c == numNodes) {
                    inBuff.reset();
                }
            } catch (IOException ioe) {
                throw new ExcepcionArchivoNoSePuedeLeer("Esto no debería " +
                        "pasar, contacte al programador...\nProblema " +
                        "Leyendo la linea " + k + " del archivo \"" +
                        fileName + "\"");
            }
        }
        if ((linea == null && c < numNodes)) {
            throw new ExcepcionInconsistenciaNumeroDeNodos("\nEl " +
                        "grafo de entrada tiene un numero de nodos distinto " +
                        "al indicado al principio del archivo:\nEncontrados " +
                        "\"" + (c+1) + "\" cursos (el "+(c+1)+"o está en la " +
                        "linea " + k + "), y se esperaban " + numNodes +
                        " cursos...");
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
            throw new ExcepcionArchivoNoSePuedeLeer("\nEsto no debería parar," +
                    " contacte con el programador...\nProblema Leyendo la"
                    + "linea " + numLine + " del archivo \"" + fileName + "\"");
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

    private static List<Arc> readArcs(BufferedReader    inBuff,
                                      String[]          names,
                                      String            fileName,
                                      int               numLinea,
                                      int               numCurConPrereq)
             throws
                    ExcepcionArchivoNoSePuedeLeer,
                    ExcepcionFormatoIncorrecto,
                    ExcepcionInconsistenciaNumeroDeNodos,
                    ExcepcionInconsistenciaNumeroDeArcos
    {
        String line = "";
        String[] prerequisitos = new String[numCurConPrereq];
        int k = 0;
        List<Arc> lista = new Lista();
        for (k = 0; k < numCurConPrereq && line != null; k++) {
            try {
                line = inBuff.readLine();
            } catch (IOException ioe) {
                throw new ExcepcionArchivoNoSePuedeLeer("\nEsto no debería " +
                        "pasar, contacte al programador...\nProblema Leyendo la"
                        + "linea " + numLinea + " del archivo \"" + fileName
                        + "\"");
            }
            prerequisitos[k] = line;
        }

        // ESTO HAY QUE BORRARLO

        System.out.println("\nreadArcs: El arreglo de lineas es:\n");
            System.out.println("{ ");
            for (int a = 0; a < prerequisitos.length; a++) {
                System.out.println(prerequisitos[a]);
            }
            System.out.println(" }\n");

        // HASTA AQUI!!!

        if (k < numCurConPrereq) {
            throw new ExcepcionFormatoIncorrecto("Problema de formato. Se es" +
                    "peraban " + numCurConPrereq + " cursos con prerequisitos" +
                    " y solo se encontraron " + k);
        } else {
            try {
                line = inBuff.readLine();
            } catch (IOException ioe) {
                throw new ExcepcionArchivoNoSePuedeLeer("\nEsto no debería " +
                        "pasar, contacte al programador...\nProblema Leyendo la"
                        + "linea " + numLinea + " del archivo \"" + fileName
                        + "\"");
            }
            if (line != null) {
                throw new ExcepcionFormatoIncorrecto("Problema de formato. " +
                        "Se esperaban " + numCurConPrereq + " cursos con " +
                        "prerequisitos y se encontraron más que estos");
            }
        }
        for (k = 0; k < prerequisitos.length; k++) {
            String[] tokens = prerequisitos[k].split(" ");
            if (2 <= tokens.length) {
                if (!tokens[1].matches("[0-9]+?")) {
                    throw new ExcepcionFormatoIncorrecto("Error de sintaxis. " +
                            "Se esperaba un numero y se encontró: " +
                            tokens[1]);
                }
                int numPre = new Integer(tokens[1]).intValue();
                if ((2 + numPre) != tokens.length) {
                    throw new ExcepcionFormatoIncorrecto("Problema de " +
                            "formato. Se esperaban " + tokens[1] +
                            " campos en la linea " + (numLinea + k) + " y " +
                            "se encontró:\n\n\t" + prerequisitos[k]);
                }
                int destino = -1;
                int fuente = -1;
                if (pertenece(tokens[0],names)) {
                    destino = Buscar.bb(names, tokens[0]);
                } else {
                    throw new ExcepcionFormatoIncorrecto("Problema con el " +
                            "nodo " + tokens[0] + ". No pertenece al grafo " +
                            "con el que se está trabajando...");
                }
                for (int i = 2; i < tokens.length; i++) {
                    // ESTO HAY QUE BORRARLO
                    System.out.println("\nreadArcs: El arreglo de nombres es:\n");
                    System.out.print("{ " + names[0]);
                    for (int a = 1; a < names.length; a++) {
                        System.out.print(", " + names[a]);
                    }
                    System.out.println(" }");

                    System.out.println("\nreadArcs: en la linea "+(k+1)+", en la iteracion "+i+", el arreglo tokens es:\n");
                    System.out.print("{ " + tokens[0]);
                    for (int a = 1; a < tokens.length; a++) {
                        System.out.print(", " + tokens[a]);
                    }
                    System.out.println(" }\n");
                    //HASTA AQUI
                    if (pertenece(tokens[i],names)) {
                        fuente = Buscar.bb(names, tokens[i]);
                        Arc arco = new Arc(fuente,destino);
                        lista.add(arco);
                        System.out.println("readArcs: Lista de arcos en construccion:\n"+lista.toString()+"\n\n\n");
                    } else {
                        throw new ExcepcionFormatoIncorrecto("Problema con el" +
                            " nodo " + tokens[i] + ". No pertenece al grafo" +
                            " con el que se está trabajando...");
                    }
                }
            } else {
                throw new ExcepcionFormatoIncorrecto("Problema de formato. " +
                        "En la linea " + (numLinea + k) + "Se esperaba una " +
                        "linea con dos o mas campos:\n (codigoMateria " +
                        "numPrereq prereq(1) prereq(2) ... prereq(numPrereq))" +
                        "\n\nSe encontró:\n\n" + prerequisitos[k]);
            }
        }
        return lista;
    }

    public static void write(String fileName) throws IOException {

    }



    /**
     * @param args the command line arguments
     */
    public static void main(String[] args) throws IOException {
        
        //Arreglo donde se guardaran los nombres de los nodos
        String[] names = null;
        DiGraph digrafo = null;

        /* Si el archivo no es del formato nombreArchivo.input, lanza la
         * excepcion.
         */
        if (args[0].matches("[[a-z][A-z][0-9][#$%&*+,-._~]]+?.input")) {
            throw new ExcepcionFormatoIncorrecto("Problema de formato en el " +
                    "nombre del archivo:\nSe esperaba un archivo con la " +
                    "extensión \".input\" y se encontró:\n\n\t\"" + args[0] +
                    "\"\n\n");
        }

        /* Si el archivo 'fileName' no existe, o no es un archivo o no se puede
         * leer, se lanza la respectiva eexcepcion.
         */
        if ((new File(args[0])).exists() &&
            (new File(args[0])).isFile() &&
            (new File(args[0])).canRead())  {
            BufferedReader inBuff = null;

            // Se inicializa el buffer de lectura
            try {
                inBuff = new BufferedReader(new FileReader(args[0]));
            } catch (FileNotFoundException fnfe) {
                throw new ExcepcionArchivoNoSePuedeLeer("Esto no deberia " +
                        "pasar, contacte al programador...\nProblema Leyendo" +
                        " el archivo \"" + args[0] + "\" al momento de crear" +
                        " el buffer lector...\n");
            }
            String linea = null;

            // Se lee la primera linea para obtener el numero de nodos...
            try {
                 linea = inBuff.readLine();
            } catch (IOException ioe) {
                throw new ExcepcionArchivoNoSePuedeLeer("Esto no deberia " +
                        "pasar, contacte al programador...\nProblema Leyendo " +
                        "la primera linea del archivo \"" + args[0] + "\"");
            }

            /* Se le pasa la primera linea a la funcion 'readFirstLine',
             * encargada de procesarla...
             */
            int numNodes = readFirstLine(linea);

            /* Ahora se leen las siguientes lineas, correspondientes a los
             * nombres de los cursos que seran representados como los nodos del
             * grafo...
             */
            names = readNames(inBuff,args[0],numNodes);
            // ESTO HAY QUE BORRARLO
            System.out.println("\nEl arreglo de nombres es:\n");
            System.out.print("{ " + names[0]);
            for (int k = 1; k < names.length; k++) {
                System.out.print(", " + names[k]);
            }
            System.out.println(" }\n");
            // HASTA AQUI

            // Se ordena el arreglo de nombres
            Ordenar.mergesortString(names);
            int numLinea = names.length + 2;
            System.out.println("\nEl arreglo de nombres es:\n");
            System.out.print("{ " + names[0]);
            for (int k = 1; k < names.length; k++) {
                System.out.print(", " + names[k]);
            }
            System.out.println(" }\n");

            /* Se procede a leer la siguiente linea, la cual contiene el numero
             * de cursos que tienen prerequisito. Este numero se guarda con el
             * fin de verificar luego inconsistencias con el numero de nodos.
             */
            int numCurConPrereq = readNumConPrereq(inBuff,args[0],numLinea);
            System.out.println("read: La cantidad de cursos con prerequisito es: " + numCurConPrereq);

            /* Se lee a continuacion las siguientes 'numCurConPrereq' lineas,
             * con el fin de fabricar una lista de los arcos a agregar en
             * nuestro digrafo...
             */
            List<Arc> arcos = readArcs(inBuff,
                                       names,
                                       args[0],
                                       numLinea,
                                       numCurConPrereq);
            System.out.println("read: La lista final es: \n" + arcos.toString());

            /* Ahora, con la información reunida, se procede a construir el
             * digrafo que va a devolver este método.
             */
            if (arcos.size() <= numNodes) {
                digrafo = new DiGraphList(numNodes);
            } else {
                digrafo = new DiGraphMatrix(numNodes);
            }
            Iterator iterador = arcos.iterator();
            System.out.println("read: Los elementos obtenidos por el iterador son:");
            while (iterador.hasNext()) {
                Arc actual = (Arc)iterador.next();
                System.out.println(actual.toString());
                Arc otro = null;
                otro = digrafo.addArc(actual);
                if (otro != null && otro.equals(actual)) {
                    System.out.println("Se agregó el arco " + actual);
                } else {
                    System.out.println("NO Se agregó el arco " + actual);
                }
            }
            System.out.println("read: El digrafo a devolver por el read es:\n"+digrafo.toString());
        } else if (!(new File(args[0])).exists()) {
            throw new ExcepcionArchivoNoExiste("Problema al leer el archivo " +
                    "\"" + args[0] +"\": EL ARCHIVO NO EXISTE!!!");
        } else if (!(new File(args[0])).isFile()) {
            throw new ExcepcionNoEsArchivo("Problema al leer el archivo \"" +
                    args[0] +"\": NO ES UN ARCHIVO!!!");
        } else if (!(new File(args[0])).canRead()) {
            throw new ExcepcionArchivoNoSePuedeLeer("Problema al leer el ar" +
                    "chivo \"" + args[0] +"\": ESTE ARCHIVO NO SE PUEDE" +
                    " LEER!!!");
        }

        // FIN DEL PROCESO DE LECTURA

        System.out.println("\nmain: El arreglo de nombres es:\n");
        System.out.print("{ " + names[0]);
        for (int a = 1; a < names.length; a++) {
            System.out.print(", " + names[a]);
        }
        System.out.println(" }");
        DiGraph result = minimo(digrafo);
        System.out.print("\nEl grafo minimo es:\n");
        System.out.println(result.toString()+"\n\n");
        //result.write(args[1]);
    }
}
