import java.io.IOException;
import java.util.Hashtable;

/**
 * DiGraph es una interfaz que determina los metodos basicos que debe tener un
 * grafo dirigido independiente de su implementacion interna
 *
 * @author Les profs
 * @version 1.0
 * @since 1.6
 **/
public abstract class DiGraph {
    protected int numNodes  = -1;
    protected int numArcs = -1;
    protected String[] nameNodes = null;

    /**
     * Agrega un arco a este DiGraphArcMatrix
     * <b>Pre</b>: {@code arco} no debe pertenecer a {@code this} y los nodos de
     * {@code arco} deben estar en {@code this}; {@code arco} no debe ser vacio
     * <b>Post</b>: El DiGraphArcMatrix contendra el arco {@code arco}
     *
     * @param arco El arco a agregar
     * @return El arco agregado, o null en caso de que los nodos src y dst no se
     * encuentren en el DiGraphArcMatrix
     *
     */
    public abstract Arc addArc(Arc arco);
    /**
     * Agrega un arco a este DiGraph
     *
     * @param src nodo fuente del arco
     * @param dst nodo destino del arco
     * @return El arco agregado
     */
    public abstract Arc addArc(int src, int dst);

    /**
     * Agrega un arco a este DiGraph
     *
     * @param src nodo fuente del arco
     * @param dst nodo destino del arco
     * @param costo del arco
     * @return El arco agregado
     */
    public abstract Arc addArc(int src, int dst, double costo);
    
    /**
     * Agrega un arco a este DiGraph
     *
     * @param src nodo fuente del arco
     * @param dst nodo destino del arco
     * @param  ident identificador del arco
     * @return El arco agregado
     */
    public abstract Arc addArc(int src, int dst, String ident);

    /**
     * Agrega un arco a este DiGraph
     *
     * @param src nodo fuente del arco
     * @param dst nodo destino del arco
     * @param costo costo del arco
     * @param  ident identificador del arco
     * @return El arco agregado
     */
    public abstract Arc addArc(int src, int dst, double costo, String ident);

    /**
     * Permite agregar <i>num</i> nuevos nodos a este DiGraph.
     *
     * @param num numero de nodos a a gregar
     */
    public abstract void addNodes(int num);


    /**
     * Remueve un arco de este DiGraph
     *
     * @param nodeIniId nodo fuente del arco a eliminar
     * @param nodeFinId nodo destino del arco a eliminar
     * @return arco eliminado, null en caso de que el arco no exista o no haya
     * sido eliminado
     */
    public abstract Arc delArc(int nodeIniId, int nodeFinId);

    /**
     * Genera una copia de este DiGraph.
     * @return una copia de este DiGraph.
     */    
    @Override
    public abstract Object clone();

    /**
     * Determina si el DiGraph g es igual a este DiGraph
     *
     * @param g el grafo con el que se quiere comparar
     * @return true si los dos DiGraph contienen los mismos nodos y los mismos
     * arcos
     */
    public abstract boolean equals(DiGraph g);

    /**
     * Retorna el Arco cuyo nodo fuente es nodoSrc y nodo destino es nodoDst.
     *
     * @param nodoSrc nodo fuente
     * @param nodoDst nodo destino
     *
     * @return Arco que va desde {@code nodoSrc} hasta {@code nodoDst}
     */
    public abstract Arc getArc(int nodoSrc, int nodoDst);

    /**
     * Retorna el grado de un nodo en este DiGraph.
     *
     * @param nodeId identificacion del nodo
     * @return el grado del nodo nodeId en este Grafo, -1 si el nodo no se
     * encuentra en el grafo
     */
    public abstract int getDegree(int nodeId);

    /**
     * Retorna el grado interno de un nodo en este DiGraph.
     *
     * @param nodeId identificacion del nodo
     * @return el grado interno del nodo nodeId en este Grafo, -1 si el nodo no
     * se encuentra en el grafo
     */
    public abstract int getInDegree(int nodeId);

    /**
     * Retorna la lista de arcos que tienen a nodeId como destino
     * @param nodeId identificador del nodo
     *
     * @return la lista de arcos que tienen a nodeId como destino
     */
    public abstract List<Arc> getInEdges(int nodeId );

/**
     * Retorna el numero de arcos en el grafo
     *
     * @return numero de arcos en el grafo
     */
    public abstract int getNumberOfArcs();

    /**
     * Retorna el numero de nodos en el grafo
     *
     * @return numero de nodos en el grafo
     */
    public abstract int getNumberOfNodes();

    
    /**
     * Retorna el grado externo de un nodo en este DiGraph.
     *
     * @param nodeId identificacion del nodo
     * @return el grado externo del nodo nodeId en este Grafo, -1 si el nodo no
     * se encuentra en el grafo
     */
    public abstract int getOutDegree(int nodeId);
   /**
     * Retorna la lista de arcos que tienen a nodeId como fuente
     * @param nodeId identificador del nodo
     *
     * @return la lista de arcos que tienen a nodeId como fuente
     */
    public abstract List<Arc> getOutEdges(int nodeId );

 
    /**
     * Retorna la lista de predecesores del nodo nodeId
     * 
     * @param nodeId el id del nodo del que se quierenlos predecesores
     * 
     * @return lista de predecesores de nodeId
     */
    
    public abstract List<Integer> getPredecesors(int nodeId);

    /**
     * Retorna la lista de sucesores del nodo nodeId
     *
     * @param nodeId el id del nodo del que se quieren los sucesores
     *
     * @return lista de sucesores de nodeId
     */
    public abstract List<Integer> getSucesors(int nodeId);

    /**
     * Indica si un arco existe en este DiGraph
     * <b>Pre</b>: {@code arco} no debe pertenecer a {@code this}, y sus nodos
     * deben pertenecer a {@code this}
     * <b>Post</b>: {@code this} tendra el arco {@code arco}
     * @param arco El arco a agregar
     * @return true si exite un arco desde el nodo src hasta el nodo dst.
     * false en caso contrario
     */
    public abstract boolean isArc(Arc arco);

    /**
     * Indica si un arco existe en este DiGraph
     * 
     * @param src el id del nodo origen del arco
     * @param dst el id del nodo destino del arco
     * @return true si exite un arco desde el nodo src hasta el nodo dst.
     * false en caso contrario
     */
    public abstract boolean isArc(int src, int dst);

    /**
     * Carga en este DiGraph, el grafo contenido en el archivo
     * 
     * @param fileName nombre del archivo que contiene la representacion del
     * grafo a cargar
     * 
     * @throws java.io.IOException
     */
    public abstract void read(String fileName) throws  IOException;

    /**
     * remueve todos los arcos de este grafo
     *
     * @return lista de arcos eliminados
     */
    public abstract List<Arc> removeAllArcs();

    /**
     * Invierte la direccion de un arco
     * @param nodeIniId nodo fuente del arco antes de invertirlo
     * @param nodeFinId nodo destino del arco antes de invertirlo
     * @return true si el arco fue invertido, false en caso contrario
     */
    public abstract boolean reverseArc(int nodeIniId, int nodeFinId);

    /**
     * Invierte todos los arcos del DiGraph.
     *
     *
     * @return true si todos los arcos fueron invertidos, false en caso 
     * contrario. En caso de que algun nodo no puede ser invertido, el grafo
     * debe quedar sin alteraciones.
     */
    public abstract boolean reverseArcs();


    /**
     * Retorna un Digraph que es la clausura transitiva de este DiGraph
     * calculada usando el algoritmo Roy-Warshal.
     *
     * Este metodo no altera este grafo <i>this</i>
     * 
     * @return un Digraph que es la clausura transitiva de este DiGraph
     * calculada usando el algoritmo Roy-Warshal
     */
   public DiGraph alcance() {
       DiGraph ret = null;

       ret = (DiGraph) this.clone();

        // Se agrega la identidad
        for( int i = 0; i < numNodes; ++i ) {
            ret.addArc(i,i);
        }

        for( int k = 0; k < numNodes; ++k ) {
            for( int i = 0; i < numNodes; ++i ) {
                if( (i != k) && ret.isArc(i,k) ) {
                    for( int j = 0; j < numNodes; ++j ) {
                        if( ret.isArc(k,j) ) {
                            ret.addArc(i,j);
                        }
                    }
                }
            }
        }

        return ret;
    }

    /**
     * Retorna la representacion en String de este DiGraph.
     * @return la representacion en String de este DiGraph.
     */
    @Override
    public abstract String toString();

    /**
     * Escribe este DiGraph en un archivo en el formato establecido en el
     * enunciado
     *
     * @param fileName nombre del archivo donde se escribira la representacion
     * del grafo
     *
     * @throws java.io.IOException
     */
    public abstract void write(String fileName) throws IOException;

    public String getName(int n) {
        if (0 <= n && n < this.nameNodes.length) {
            return this.nameNodes[n];
        } else {
            return "";
        }
    }

    public int getNumber(String name) {
        int posicion = this.bb(nameNodes, name);
        if (0 <= posicion && posicion < this.nameNodes.length &&
                this.nameNodes[posicion].equals(name)) {
            return posicion;
        } else {
            return -1;
        }
    }

    public void setNames(String[] noms) 
            throws ExcepcionInconsistenciaNumeroDeNodos
    {
        if (noms.length == this.numNodes) {
            Ordenar.mergesortString(noms);
            this.nameNodes = noms;
        } else {
            throw new ExcepcionInconsistenciaNumeroDeNodos("El numero de " +
                    "nodos actual no coincide con el del arreglo de entrada!");
        }
    }

    public String[] getNames() {
        return this.nameNodes;
    }

    // OPERACIONES INTERNAS PRIVADAS AUXILIARES:

    /**
     * Implementa la busqueda binaria en arreglos de Strings. Mas eficiente que
     * la busqueda lineal. Requiere que exista una relacion de orden para el
     * tipo de elementos del arreglo y que el arreglo de entrada este ordenado.
     * @param a el arreglo de Strings a leer.
     * @param s el elemento de tipo String a buscar en 'a'
     * @return posicion en la que se consiguio 's' en caso de estar en 'a'.
     *         Si 's' no esta en 'a', devuelve la posicion donde deberia estar
     *         el elemento 's'.
     */
    /*@ requires (this.tam>=0) &&
      @          (\forall int i; 0 <= i && i < this.tam - 1;
      @                a[i].compareTo(a[i+1]) <= 0
      @          );
      @
      @ ensures (0 <= \result && \result <= this.tam);
      @ ensures (0 <= \result && \result < this.tam && a[\result].equals(s))
      @         ==>
      @         (\exists int i ; 0 <= i && i < this.tam;
      @                 (\forall int j; 0 <= j && j < this.tam && i != j;
      @                         a[i].compareTo(s) == 0 &&
      @                         a[i].compareTo(a[j]) != 0
      @                 )
      @         );
      @ ensures (0 <= \result && \result < this.tam && !a[\result].equals(s))
      @         ==>
      @         (
      @             (\forall int i ; 0 <= i && i < this.tam;
      @                         a[i].compareTo(s) != 0
      @             )
      @             &&
      @             (\forall int i; 0 <= i && i < \result;
      @                         a[i].compareTo(s) < 0
      @             )
      @             &&
      @             (\forall int j; \result <= j && j < this.tam;
      @                         s.compareTo(a[j]) < 0
      @             )
      @         );
      @ ensures (\forall int i; 0 <= i && i < this.tam; a[i].compareTo(s) < 0)
      @         ==>
      @         ( \result == this.tam );
      @ ensures ( (this.tam == 0) ==> (\result == 0) );
      @*/
    private /*@ spec_public pure @*/ int bb (String a[], String s) {
        int     pos=0;
        int     izq=0;
        int     der  = a.length;
        boolean esta = false;
        /*@ loop_invariant 0 <= izq && izq <= der && der <= this.tam &&
          @                ( esta || (\exists int i; izq <= i && i < der;
          @                                a[i].equals(s)
          @                          )
          @                          <==>
          @                          (\exists int i; 0 <= i &&
          @                                          i < this.tam;
          @                                a[i].equals(s)
          @                          )
          @                ) &&
          @                (
          @                     (esta ==> (0 <= pos && pos < this.tam &&
          @                                 a[pos].equals(s)
          @                                )
          @                     )
          @                     &&
          @                     ((izq == der && !esta) ==>
          @                         (\forall int i,j;
          @                             0 <= i && i < pos && pos <= j &&
          @                                 j < this.tam;
          @                                     a[i].compareTo(s) < 0 &&
          @                                     s.compareTo(a[j]) < 0
          @                         )
          @                     )
          @                );
          @
          @ decreasing (der-izq)+(!esta ? 1:0);
          @*/
        while (izq!=der && !esta) {
            int med=(izq+der)/2;
            if (a[med].equals(s)) {
                esta=true;
            } else if (a[med].compareTo(s)<0) {
                izq=med+1;
            } else if (a[med].compareTo(s)>0) {
                der=med;
            }
            pos = ( esta ? med : der);
        }
        return pos;
    }
}