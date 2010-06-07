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
        DiGraph ret = null;
        if (grafo.numNodes < grafo.numArcs) {
            ret = (DiGraphMatrix) grafo.clone();
        } else {
            ret = (DiGraphList) grafo.clone();
        }

        // Se calcula el alcance del grafo para usarlo como punto de partida
        ret = ret.alcance();

        // Se agrega la identidad
        for( int i = 0; i < ret.numNodes; ++i ) {
            ret.delArc(i, i);
        }

        // Se eliminan los arcos transitivos
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
        
        return ret;
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
                        " hay un error de sintaxis:\nSe esperaba un numero" +
                        " (numCursos) y se encontró: \"" + tokens[0] + "\"\n");
            }
        } else {
            throw new ExcepcionFormatoIncorrecto("En la primera linea hay " +
                    "un error de sintaxis:\nSe esperaban un sólo elemento (" +
                    "numCursos), y se encontró:\n\t\"" + line + "\"");
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
                throw new ExcepcionFormatoIncorrecto("En la linea " + numLine +
                        " donde debe decir el número de cursos que tienen" +
                        " prerequisito, hay un error de sintaxis: Se esperaba" +
                        " un numero (numCursosConPrerequisito) y se encontro: "+
                        "\n\t\"" + tokens[0] + "\"\n\nEsto puede ser un mero " +
                        "error de sintaxis o deberse a que hay más cursos " +
                        "escritos en el archivo que los indicados en la " +
                        "primera linea. Por favor, revise el archivo de " +
                        "entrada (" + fileName + ")");
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
                    if (pertenece(tokens[i],names)) {
                        fuente = Buscar.bb(names, tokens[i]);
                        Arc arco = new Arc(fuente,destino);
                        lista.add(arco);
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


    /**
     * Escribe la representacion de este DiGraph en el archivo {@code fileName},
     * usando el formato siguiente:
     * <blockquote>
     * <p><b>Sintaxis</b>:</p>
     * <p>numNodos numArcos</p>
     * <p>nodoSrc nodoDst</p>
     * <p>nodoSrc nodoDst</p>
     * <p>nodoSrc nodoDst</p>
     * <p>   .       .   </p>
     * <p>   .       .   </p>
     * <p>   .       .   </p>
     * <p>nodoSrc nodoDst</p>
     * </blockquote>
     * <b>pre</b>: {@code fileName} debe existir, ser un archivo, y poder
     * escribirse.
     * <b>post</b>: El archivo {@code fileName} contiene la representación de
     * este DiGraph.
     * @param fileName Archivo a escribir
     * @throws IOException En caso de que el archivo {@code fileName} no exista,
     * no sea un archivo o no se pueda escribir en el.
     */
    public static void write(String fileName, String[] nombres, DiGraph digrafo)
                                                            throws IOException
    {
        File output = new File(fileName);
        if (output.exists()) {
            output.delete();
            output.createNewFile();
        } else {
            output.createNewFile();
        }

        // Se crea el flujo de salida de impresión
        PrintStream out;
        try {
            out = new PrintStream(output);
        } catch (FileNotFoundException fnfe) {
            throw new ExcepcionArchivoNoSePuedeEscribir("\nEsto no deberia" +
                    " pasar, contacte al programador...Problema escribiendo" +
                    " en el archivo \"" + fileName + "\"");
        }

        try {
            // Se imprime linea a linea el archivo...
            for (int i = 0; i < digrafo.numNodes; i++) {
                List<Integer> pred = digrafo.getPredecesors(i);
                String[] linea = new String[pred.size()];
                for (int k = 0; k < linea.length; k++) {
                    linea[k] = nombres[pred.get(k).intValue()];
                }
                Ordenar.mergesortString(linea);
                out.print(nombres[i]);
                out.print(" " + linea.length);
                for (int k = 0; k < linea.length; k++) {
                    out.print(" " + linea[k]);
                }
                out.print("\n");
            }
        } catch (NullPointerException npe) {
            throw new NullPointerException("Error al intentar trabajar con un" +
                    "digrafo vacío...");
        }
    }


    /**
     * @param args the command line arguments
     */
    public static void main(String[] args) throws IOException {

        /* Primero se verifica que se haya pasado como parámetro el nombre del
         * archivo a leer, comprobando la longitud del arreglo de argumentos, y
         * la existencia de el argumento requerido para el funcionamiento del
         * programa.
         */
        if (1 <= args.length && args[0] != null) {
            //Arreglo donde se guardaran los nombres de los nodos
            String[] names = null;
            DiGraph digrafo = null;
            String inputFile = args[0];

            /* Si el archivo no es del formato nombreArchivo.input, lanza la
             * excepcion. Para verificar esto, analizamos la cadena de entrada:
             */
            String outputFile = "";
            if (inputFile.substring(inputFile.length() - 5).equals("input")) {
                outputFile = inputFile.substring(0, inputFile.length() - 5)
                        + "output";
            } else {
                throw new ExcepcionFormatoIncorrecto("Problema de formato en el"
                        + " nombre del archivo:\nSe esperaba un archivo con la "
                        + "extensión \".input\" y se encontró:\n\n\t\"" +
                        inputFile + "\"\n\n");
            }

            /* Si el archivo 'fileName' no existe, o no es un archivo o no se
             * puede leer, se lanza la respectiva eexcepcion.
             */
            if ((new File(inputFile)).exists()
                    && (new File(inputFile)).isFile()
                    && (new File(inputFile)).canRead()) {
                BufferedReader inBuff = null;

                // Se inicializa el buffer de lectura
                try {
                    inBuff = new BufferedReader(new FileReader(inputFile));
                } catch (FileNotFoundException fnfe) {
                    throw new ExcepcionArchivoNoSePuedeLeer("Esto no deberia " +
                            "pasar, contacte al programador...\nProblema " +
                            "leyendo el archivo \"" + inputFile + "\" al " +
                            "momento de crear el buffer lector...\n");
                }
                String linea = null;

                // Se lee la primera linea para obtener el numero de nodos...
                try {
                    linea = inBuff.readLine();
                } catch (IOException ioe) {
                    throw new ExcepcionArchivoNoSePuedeLeer("Esto no deberia "
                            + "pasar, contacte al programador...\nProblema " +
                            "leyendo la primera linea del archivo \"" +
                            inputFile + "\"");
                }

                /* Se le pasa la primera linea a la funcion 'readFirstLine',
                 * encargada de procesarla...
                 */
                int numNodes = readFirstLine(linea);

                /* Ahora se leen las siguientes lineas, correspondientes a los
                 * nombres de los cursos que seran representados como los nodos
                 * del grafo...
                 */
                names = readNames(inBuff, inputFile, numNodes);

                // Se ordena el arreglo de nombres
                Ordenar.mergesortString(names);
                int numLinea = names.length + 2;

                /* Se procede a leer la siguiente linea, la cual contiene el
                 * numero de cursos que tienen prerequisito. Este numero se
                 * guarda con el fin de verificar luego inconsistencias con el
                 * numero de nodos.
                 */
                int numCurConPrereq = readNumConPrereq (inBuff,
                                                        inputFile,
                                                        numLinea);

                /* Se lee a continuacion las siguientes 'numCurConPrereq'
                 * lineas, con el fin de fabricar una lista de los arcos a
                 * agregar en nuestro digrafo...
                 */
                List<Arc> arcos = readArcs(inBuff,
                        names,
                        inputFile,
                        numLinea,
                        numCurConPrereq);

                /* Ahora, con la información reunida, se procede a construir el
                 * digrafo que va a devolver este método.
                 */
                if (numNodes < arcos.size()) {
                    digrafo = new DiGraphMatrix(numNodes);
                } else {
                    digrafo = new DiGraphList(numNodes);
                }

                // Ahora se agregan los arcos al digrafo...
                Iterator iterador = arcos.iterator();
                while (iterador.hasNext()) {
                    Arc actual = (Arc) iterador.next();
                    digrafo.addArc(actual);
                }
                // YA ESTÁ CONSTRUIDO NUESTRO DIGRAFO!!!

            } else if (!(new File(inputFile)).exists()) {
                throw new ExcepcionArchivoNoExiste("Problema al leer el archivo"
                        + " \"" + inputFile + "\": EL ARCHIVO NO EXISTE!!!");
            } else if (!(new File(inputFile)).isFile()) {
                throw new ExcepcionNoEsArchivo("Problema al leer el archivo \""
                        + inputFile + "\": NO ES UN ARCHIVO!!!");
            } else if (!(new File(inputFile)).canRead()) {
                throw new ExcepcionArchivoNoSePuedeLeer("Problema al leer el ar"
                        + "chivo \"" + inputFile + "\": ESTE ARCHIVO NO SE "
                        + "PUEDE LEER!!!");
            }
            // FIN DEL PROCESO DE LECTURA

            /* Se calcula el digrafo minimo; digrafo en el cual se eliminan
             * todos los arcos transitivos y reflexivos, quedando cada nodo
             * incidido sólo por sus predecesores inmediatos.
             */
            DiGraph result = minimo(digrafo);

            /* Ahora se procede a escribir el digrafo calculado en el archivo de
             * salida.
             */
            write(outputFile,names,result);
            //Fin del programa...

        } else {
            System.err.println("\nSintaxis:\n\n\tjava Main nombre_del_" +
                    "archivo_de_entrada.input\n\n\t\tNuestro programa " +
                    "generará un archivo de igual nombre y extensión " +
                    "\".output\" en el\n\tcual estará escrito el resultado " +
                    "de los cálculos de acuerdo al formato establecido en " +
                    "la\n\tcátedra.\n\n\nFormato De Entrada:\n\n\nnumCursos\n" +
                    "curso(1)\ncurso(2)\ncurso(3)\n.\n.\n.\ncurso(numCursos)" +
                    "\nnumCursosC/Prereq\ncursoC/Prereq(1) numPrereq " +
                    "prereq(1) prereq(2) prereq(3) . . . . prereq(numPrereq)\n"+
                    "cursoC/Prereq(2) numPrereq prereq(1) prereq(2) " +
                    "prereq(3) . . . . prereq(numPrereq)\ncursoC/Prereq(3) " +
                    "numPrereq prereq(1) prereq(2) prereq(3) . . . . " +
                    "prereq(numPrereq)\n.\n.\n.\n" +
                    "cursoC/Prereq(numCursosC/Prereq) numPrereq prereq(1) " +
                    "prereq(2) prereq(3) . . . . prereq(numPrereq)\n\n\n" +
                    "Formato De Salida:\n\n\ncurso(1) numPrereq prereq(1) " +
                    "prereq(2) prereq(3) . . . . prereq(numPRereq)\ncurso(2) " +
                    "numPrereq prereq(1) prereq(2) prereq(3) . . . . " +
                    "prereq(numPRereq)\ncurso(3) numPrereq prereq(1) " +
                    "prereq(2) prereq(3) . . . . prereq(numPRereq)" +
                    "\n.\n.\n.\n.");
        }
    }
}
