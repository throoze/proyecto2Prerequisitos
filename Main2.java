
import java.io.IOException;

public class Main2 {
    public static void main (String args[]) {
        String inFile = args[0];
        DiGraphList digrafl = null;
        DiGraphMatrix digrafm = null;
        try {
            digrafl = new DiGraphList(inFile);
        } catch (IOException ex) {
            System.out.println("Problema inicializando el DiGraphList");
            System.out.println(ex.getMessage());
            System.out.println(ex.getStackTrace());
            System.out.println("\n\n\n");
        }
        try {
            digrafm = new DiGraphMatrix(inFile);
        } catch (IOException ex) {
            System.out.println("Problema inicializando el DiGraphMatrix");
            System.out.println(ex.getMessage());
            System.out.println(ex.getStackTrace());
            System.out.println("\n\n\n");
        }

        digrafl.addArc(new Arc(3,4));
        digrafl.addArc(3, 5);
        digrafl.addArc(0, 2, "nuevo1");
        digrafl.addArc(0, 3, 9.4);
        digrafl.addArc(0, 4, 5.4, "nuevo2");

        digrafm.addArc(new Arc(3,4));
        digrafm.addArc(3, 5);
        digrafm.addArc(0, 2, "nuevo1");
        digrafm.addArc(0, 3, 9.4);
        digrafm.addArc(0, 4, 5.4, "nuevo2");


        DiGraphList nuevol = digrafl.clone();
        DiGraphMatrix nuevom = digrafm.clone();


        nuevol.addNodes(3);
        System.out.println("Nuevo lista con mas nodos:\n\n"+nuevol.toString());
        nuevom.addNodes(3);
        System.out.println("Nuevo matrix con mas nodos:\n\n"+nuevom.toString());


        DiGraph alcancel = digrafl.alcance();
        DiGraph alcancem = digrafm.alcance();

        Arc delarcl = digrafl.delArc(3, 5);
        if (delarcl == null) {
            System.out.println("No se borró el arco en el de lista");
        } else if (delarcl.equals(new Arc(3,5))) {
            System.out.println("Si se borró el arco en el de lista");
        } else {
            System.out.println("Si se borró el arco en el de lista, pero algo NO funciona");
        }

        Arc delarcm = digrafm.delArc(3, 5);
        if (delarcm == null) {
            System.out.println("No se borró el arco en el de matrix");
        } else if (delarcm.equals(new Arc(3,5))) {
            System.out.println("Si se borró el arco en el de matrix");
        } else {
            System.out.println("Si se borró el arco en el de matrix, pero algo NO funciona");
        }

        System.out.println("El DiGraphList " + (digrafl.equals(digrafm)? "SI" : "NO") + " es igual al DiGraphMatrix");
        System.out.println("El DiGraphMatrix " + (digrafm.equals(digrafl)? "SI" : "NO") + " es igual al DiGraphList");


        Arc arcol = digrafl.getArc(6, 1);
        if (arcol == null) {
            System.out.println("No se consiguió el arco en el de lista");
        }
        Arc arcom = digrafm.getArc(6, 1);
        if (arcom == null) {
            System.out.println("No se consiguió el arco en el de matrix");
        }

        int gradol = digrafl.getDegree(4);
        System.out.println("El grado del nodo 4 de el de lista es " + gradol);
        int gradom = digrafm.getDegree(4);
        System.out.println("El grado del nodo 4 de el de matrix es " + gradom);


        List<Arc> incidentesl = digrafl.getInEdges(4);
        System.out.println("Los incidentes en el nodo 4 del de lista son:\n"+incidentesl.toString());
        List<Arc> incidentesm = digrafm.getInEdges(4);
        System.out.println("Los incidentes en el nodo 4 del de matrix son:\n"+incidentesm.toString());


        System.out.println("El de lista tiene " + digrafl.getNumberOfArcs() + " arcos");
        System.out.println("El de matrix tiene " + digrafm.getNumberOfArcs() + " arcos");


        System.out.println("El de lista tiene " + digrafl.getNumberOfNodes() + " nodos");
        System.out.println("El de matrix tiene " + digrafm.getNumberOfNodes() + " nodos");

        List<Arc> salientesl = digrafl.getOutEdges(4);
        System.out.println("Los salientes del nodo 4 del de lista son:\n"+salientesl.toString());
        List<Arc> salientesm = digrafm.getOutEdges(4);
        System.out.println("Los salientes del nodo 4 del de matrix son:\n"+salientesm.toString());
        
        List<Integer> predecesorl = digrafl.getPredecesors(4);
        System.out.println("Los predecesores del nodo 4 del de lista son:\n"+predecesorl.toString());
        List<Integer> predecesorm = digrafm.getPredecesors(4);
        System.out.println("Los predecesores del nodo 4 del de matrix son:\n"+predecesorm.toString());

        System.out.println("El arco (8,3) " + (digrafl.isArc(new Arc(8,3)) ? "SI" : "NO") + " pertenece al de lista");
        System.out.println("El arco (8,3) " + (digrafm.isArc(new Arc(8,3)) ? "SI" : "NO") + " pertenece al de matrix");

        System.out.println("El arco (8,3) " + (digrafl.isArc(8,3) ? "SI" : "NO") + " pertenece al de lista");
        System.out.println("El arco (8,3) " + (digrafm.isArc(8,3) ? "SI" : "NO") + " pertenece al de matrix");


        if (digrafl.reverseArc(7, 0)) {
            System.out.println("El arco (7,0) ahora es (0,7) en el de lista");
        } else {
            System.out.println("El arco (7,0) no se invirtió en el de lista");
        }
        if (digrafm.reverseArc(7, 0)) {
            System.out.println("El arco (7,0) ahora es (0,7) en el de matrix");
        } else {
            System.out.println("El arco (7,0) no se invirtió en el de matrix");
        }

        DiGraph inversol = digrafl.clone();
        DiGraph inversom = digrafm.clone();

        System.out.println("El de lista antes de invertir:\n\n"+inversol.toString());
        if (inversol.reverseArcs()) {
            System.out.println("El DiGraphList se invirtió");
        } else {
            System.out.println("El DiGraphList NO se invirtió");
        }
        System.out.println("El de lista después de invertir:\n\n"+inversol.toString());

        System.out.println("El de matrix antes de invertir:\n\n"+inversom.toString());
        if (inversom.reverseArcs()) {
            System.out.println("El DiGraphMatrix se invirtió");
        } else {
            System.out.println("El DiGraphMatrix NO se invirtió");
        }
        System.out.println("El de matrix después de invertir:\n\n"+inversom.toString());

        System.out.println("\nEl DiGraphList inverso " + (inversol.equals(inversom)? "SI" : "NO") + " es igual al DiGraphMatrix inverso");
        System.out.println("\nEl DiGraphMatrix inverso " + (inversom.equals(inversom)? "SI" : "NO") + " es igual al DiGraphList inverso");


        List<Arc> invarcsl = inversol.removeAllArcs();
        System.out.println("Los arcos invertidos del de list son:\n\n" + invarcsl.toString());
        List<Arc> invarcsm = inversom.removeAllArcs();
        System.out.println("Los arcos invertidos del de matrix son:\n\n" + invarcsm.toString());

        System.out.println("Los digrafos quedaron asi:\n\nEl DiGraphList es:\n\n"+digrafl.toString()+"\n\nEl DiGraphMatrix es:\n\n"+digrafm.toString());

        System.out.println("\n\nEsto es todo!!!! se probaron todas las operaciones con éxito!");

        try {
            digrafl.write("lista.output");
        } catch (IOException ex) {
            System.out.println("Problema escribiendo el DiGraphList");
            System.out.println(ex.getMessage());
            System.out.println(ex.getStackTrace());
            System.out.println("\n\n\n");
        }
        try {
            digrafm.write("matrix.output");
        } catch (IOException ex) {
            System.out.println("Problema escribiendo el DiGraphMatrix");
            System.out.println(ex.getMessage());
            System.out.println(ex.getStackTrace());
            System.out.println("\n\n\n");
        }
    }
}