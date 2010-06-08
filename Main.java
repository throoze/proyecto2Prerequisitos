import java.io.IOException;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.PrintStream;
import java.util.Iterator;

/**
 * Clase principal que se encarga de calcular los prerequisitos inmediatos de un
 * conjunto de cursos junto con sus prerequisitos representando este problema
 * mediante un DiGraph. La entrada y salida cumple con el formato especificado
 * en la cátedra.
 * @author Victor De Ponte, 05-38087
 * @author Karina Valera, 06-40414
 * @version 2.0
 * @since 1.6
 * @see DiGraph, DiGraphMatrix, DiGraphList, Arc, List, Lista
 */
public class Main {
    
    /**
     * Se encarga de calcular el DiGraph sin arcos transitivos asociado al
     * {@code DiGraph digrafo}.
     * <b>Pre</b>: true;
     * <b>Post</b>: el digrafo resultante es el mismo que el de entrada sin
     * ninguno de sus arcos transitivos.
     * @param digrafo {@code DiGraph} sobre el cual se calculará el digrafo
     * minimo.
     * @return El {@code DiGraph} minimo  asociado al digrafo de entrada.
     */
    private static DiGraph minimo (DiGraph digrafo) {
        DiGraph ret = null;
        if (digrafo.numNodes < digrafo.numArcs) {
            ret = (DiGraphMatrix) digrafo.clone();
        } else {
            ret = (DiGraphList) digrafo.clone();
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

    /**
     * Determina si el {@code String elem} pertenece al arreglo {@code arr}
     * <b>Pre</b>: true
     * <b>Post</b>: el resultado es true si elem esta en arr. false en caso
     * contrario
     * @param elem Elemento a buscar
     * @param arr Arreglo donde se buscara el elemento elem
     * @return true si {@code elem} esta en {@code arr}. false en caso contrario
     */
    private static boolean pertenece(String elem, String[] arr) {
        boolean pertenece = false;
        int pos = Buscar.bb(arr, elem);
        if (0 <= pos && pos < arr.length && arr[pos].equals(elem)) {
            pertenece = true;
        }
        return pertenece;
    }

    /**
     * Se encarga de interpretar la primera linea del archivo de entrada basado
     * en el formato establecido por la cátedra.
     * <b>Pre</b>: {@code line} debe contener un numero, el cual esta en la
     * primera linea del archivo de entrada
     * <b>Post</b>: devuelve el número contenido en la linea {@code line} o
     * arroja una excepcion.
     * @param line String a verificar
     * @return un numero el cual esta contenido en la linea {@code line}
     * @throws ExcepcionFormatoIncorrecto En caso de que el {@code Strin line}
     * tenga varios elementos o no sea un numero
     */
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

    /**
     * Se encarga de leer la segunda sección del archivo de entrada, a travez de
     * un  {@code BufferedReader} ya abierto y en la linea apropiada.
     * <b>Pre</b>: el buffer de entrada debe estar en la segunda linea y a
     * partir de esta debe haber {@code numNodes} lineas que contienen nombres
     * de cursos.
     * <b>Post</b>: El resultado es un arreglo que contiene los nombres
     * mencionados en <b>Pre</b>.
     * @param inBuff BufferReader de entrada. Debe estar en la segunda linea
     * @param fileName Nombre del archivo que se esta leyendo
     * @param numNodes Número de lineas a leerse por éste método
     * @return Un arreglo que contiene los nombres leidos a travez de
     * {@code inBuff}
     * @throws ExcepcionArchivoNoSePuedeLeer En caso de que {@code fileNAme} no
     * se pueda leer
     * @throws ExcepcionFormatoIncorrecto En caso de que haya algun error de
     * formato leida por el buffer
     * @throws ExcepcionInconsistenciaNumeroDeNodos En caso de que haya menos
     * nodos de los indicados por {@code numNodes}
     */
    private static String[] readNames (BufferedReader inBuff,
                                       String         fileName,
                                       int            numNodes)
            throws ExcepcionArchivoNoSePuedeLeer,
                   ExcepcionFormatoIncorrecto,
                   ExcepcionInconsistenciaNumeroDeNodos
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

    /**
     * Se encarga de leer la tercera sección del archivo de entrada, la sección
     * que contiene el numero de cursos con prerequisito, a travez del mismo
     * buffer abierto anteriormente por otros métodos.
     * <b>Pre</b>: {@code inBuff} debe haber sido inicializado y manipulado
     * hasta estar en la linea adecuada, {@code fileName} debe existir, ser un
     * archivo y ser legible, y cumplir con el formato establecido en la cátedra
     * y {@code numLine} debe ser el numero de la linea a leer donde se
     * encuentre el numero buscado.
     * <b>Post</b>: Se devolvera el numero de cursos con prerequisito o se
     * lanzará la excepción correspondiente en caso de haber uno de los errores
     * ya mencionados.
     * @param inBuff BufferReader de entrada. Debe haber sido ya inicializado y
     * manipulado hasta estar en la linea adecuada.
     * @param fileName Nombre del archivo leido por {@code inBuff}
     * @param numLine Numero de la linea en la cual empieza la lectura de esta
     * sección
     * @return el numero de cursos que tienen prerequisitos
     * @throws ExcepcionFormatoIncorrecto en caso de que se encuentre mas de un
     * elemento, o algo distinto de un número.
     * @throws ExcepcionArchivoNoSePuedeLeer En caso de que el ar.chivo
     * {@code fileName} no se pueda leer por algun error de entrada/salida.
     */
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

    /**
     * Se encarga de leer la última sección del archivo de entrada, en la cual
     * se representan los arcos que pertenecerán a nuestro DiGraph.
     * <b>Pre</b>: El buffer de entrada ({@code inBuff}) debe haberse leido
     * hasta la linea adecuada, en la cual compienza la sección a ser leída;
     * {@code names} debe contener los nombres de los nodos que compondrán el
     * DiGraph a construir ordenados lexicográficamente, {@code fileName} debe
     * ser el nombre del archivo leido, {@code numLinea} debe ser la linea de
     * {@code fileName} en la cual se empieza a leer y {@code numCurConPrereq}
     * debe ser la cantidad de lineas que se espera leer.
     * <b>Post</b>:Se devolverá una lista con cada uno de los arcos leidos en el
     * proceso.
     * @param inBuff {@code BufferedReader} de entrada sobre el cual se
     * efectuará la lectura
     * @param names Arreglo que contiene los nombres de los nodos con los cuales
     * se estará trabajando, ordenado lexicográficamente.
     * @param fileName Nombre del archivo que está siendo leído
     * @param numLinea Número de linea de {@code fileName} en la cual se
     * comienza a leer en este método
     * @param numCurConPrereq Cantidad de lineas que se espera leer
     * @return Una {@code List(Arc)} que contendrá todos los arcos a ser
     * agregados a nuestro DiGraph
     * @throws ExcepcionArchivoNoSePuedeLeer En caso de que ocurra un error
     * leyendo el BufferedReader
     * @throws ExcepcionFormatoIncorrecto En caso de que el formato encontrado
     * no concuerde con el establecido por la cátedra
     * @throws ExcepcionInconsistenciaNumeroDeNodos En caso de que se utilice un
     * nodo que no pertenezca al arreglo de nombres, y por ende, al DiGraph que
     * se está construyendo.
     */
    private static List<Arc> readArcs(BufferedReader    inBuff,
                                      String[]          names,
                                      String            fileName,
                                      int               numLinea,
                                      int               numCurConPrereq)
             throws
                    ExcepcionArchivoNoSePuedeLeer,
                    ExcepcionFormatoIncorrecto,
                    ExcepcionInconsistenciaNumeroDeNodos
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
     * usando el formato determinado por la cátedra.
     * <b>Pre</b>: {@code nombres} debe contener los nombres de los nodos del
     * DiGraph digrafo, ordenados lexicográficamente.
     * <b>Post</b>: El archivo {@code fileName} contiene la representación de
     * este DiGraph según el formato determinado por la cátedra.
     * @param fileName Archivo a escribir
     * @throws IOException En caso de que el archivo {@code fileName} no se
     * pueda crear, o no se pueda escribir.
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
     * Método principal que se encarga de hacer las llamadas a los demás métodos
     * para leer el archivo de origen, hacer los cálculos, y luego escribir el
     * resultado en un nuevo archivo. Todo el proceso está comentado.
     * <b>Pre</b>:Se debe pasar al menos un parámetro. De todos los parámetros
     * pasados, sólo se tomará en cuenta el primero, el cual representa el
     * nombre o la ruta (absoluta o relativa) del archivo a ser leido, el cuál
     * deberá tener extensión '.input' y contener la representacion del DiGraph
     * aa procesar según el formato de entrada establecido por la cátedra.
     * <b>Post</b>: Se generará un nuevo archivo con el mismo nombre que el
     * archivo de entrada, pero con extensión '.output', el cual contendrá la
     * representación del DiGraph calculado de acuerdo al formato de salida
     * establecido por la cátedra. En caso de que ocurra algun error de
     * entrada/salida, se lanzará la excepción adecuada. En caso de ocurrir un
     * error de sintaxis al invocar el programa, éste sólo devolverá un mensaje
     * y terminará.
     * @param args Arreglo con los argumentos pasados al programa.
     * @throws IOException En caso de que El archivo de entrada no exista, o no
     * sea un archivo, o no se pueda leer, o haya una inconsistencia en el
     * número de nodos usados en el archivo de entrada o haya un error de
     * formato en el archivo de entrada. Cada tipo de excepción lanzada por éste
     * programa tiene su nombre y mensaje explicito y amigable, y todas heredan
     * de {@code IOException}
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