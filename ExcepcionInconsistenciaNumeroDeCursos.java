import java.io.IOException;

/**
 * Excepcion que es lanzada en caso de que en el archivo pasado como parámetro
 * haya una inconsistencia entre el número de arcos indicados y el número de
 * arcos utilizados.
 * @author Victor De Ponte, 05-38087
 * @author Karina Valera, 06-40414
 * @version 2.0
 * @since 1.6
 */
public class ExcepcionInconsistenciaNumeroDeCursos extends IOException {

    /**
     * Crea una nueva {@code ExcepcionInconsistenciaNumeroDeCursos} vacía.
     * <b>Pre</b>: {@code true}
     * <b>Post</b>: esta {@code ExcepcionInconsistenciaNumeroDeCursos} esta
     * vacia.
     */
    public ExcepcionInconsistenciaNumeroDeCursos() {
        super();
    }

    /**
     * Crea una nueva {@code ExcepcionInconsistenciaNumeroDeCursos} con un
     * mensaje asociado.
     * <b>Pre</b>: {@code true}
     * <b>Post</b>: esta {@code ExcepcionInconsistenciaNumeroDeCursos} contiene
     * el mensaje {@code msg}.
     * @param msg mensaje lanzado al usuario
     */
    public ExcepcionInconsistenciaNumeroDeCursos(String msg) {
        super(msg);
    }

    /**
     * Crea una nueva {@code ExcepcionInconsistenciaNumeroDeCursos} con un
     * mensaje y una causa asociados.
     * <b>Pre</b>: {@code true}
     * <b>Post</b>: esta {@code ExcepcionInconsistenciaNumeroDeCursos} contiene
     * el mensaje {@code msg} y la causa {@code cause}.
     * @param msg mensaje lanzado al usuario
     * @param cause la causa de la excepción
     */
    public ExcepcionInconsistenciaNumeroDeCursos(String msg, Throwable cause) {
        super(msg,cause);
    }
}
