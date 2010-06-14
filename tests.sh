#!/bin/bash
# Hacer un test con los casos de prueba del proyecto 2

shopt -s extglob

echo "Compilando..."
javac *.java 2> /dev/null
echo "Hecho!!!"
echo "Creando archivos temporales..."
for i in $(ls repo/*.input)
do
    cp $i .
done

echo "Realizando los calculos"
for i in $(ls *.input)
do
    if (java Main $i 2> /dev/null)
    then
        echo "Corrida caso $i [OK]"
    else
        echo "Corrida caso $i [OK]"
    fi
done

echo -e "\n\n\nIniciando las comparaciones:\n"
for i in $(ls *.output)
do
    if (diff $i repo/$i)
    then
        echo -e "Caso $i [Ok]"
    else
        echo -e "Caso $i [Error]"
    fi
done

echo -e "\n\nBorrando archivos temporales..."
rm *.input
rm *.output
rm *.class
echo "Tareas realizadas!!! Hasta luego"
