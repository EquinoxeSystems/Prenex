/****************************************************************************/
/*                         CONJUNTO.H: Clase Conjunto                       */
/*                   versi¢n 2.0 para Turbo C++ y Borland C++               */
/*                                                                          */
/*   Realizado por: Rodolfo Gonz lez Gonz lez.                              */
/****************************************************************************/

// Este header (archivo de inclusi¢n) desarrolla una clase (conjunto) para el
// manejo de conjuntos estilo Turbo Pascal, de hasta 255 elementos enteros.
// De hecho se puede almacenar en un objeto de ‚sta clase cualquier enumera-
// ci¢n. Proporciona operadores para uni¢n, intersecci¢n, igualdad, etc. de
// conjuntos. Fu‚ desarrollado en Turbo C++ 3.0.
// Copyright 1995 Rodolfo Gonz lez Gonz lez.

#include <iostream.h>

const MaxCard = 255;

typedef enum Boolean {FALSE,TRUE};

class conjunto {
         int elems[MaxCard];
         int card;
    public:
                         conjunto (void) { card = 0; }
                int      cardin (void) { return this->card; }
                void     vacio (void) { this->card = 0; }
         conjunto conjunto::operator = (int);
         conjunto conjunto::operator = (conjunto&);

         friend Boolean  operator &  (int, conjunto&);
         friend Boolean  operator &  (conjunto&, int);
         friend Boolean  operator == (conjunto&, conjunto&);
         friend Boolean  operator != (conjunto& c1, conjunto& c2) /*desigualdad*/
                                                       { return !(c1 == c2); }
         friend Boolean  operator <= (conjunto&, conjunto&);
         friend Boolean  operator >= (conjunto& c1, conjunto& c2) //superconjunto
                                                          { return c2 <= c1; }
         friend Boolean  operator <  (conjunto& c1, conjunto& c2) /*subconjunto
                              propio */ { return ((c1 <= c2) && (c1 != c2)); }
         friend conjunto operator +  (conjunto&, conjunto&);
         friend conjunto operator +  (conjunto& c, int e) { return c = e; }
         friend conjunto operator -  (conjunto&, int);
         friend conjunto operator -  (conjunto&, conjunto&);
         friend conjunto operator *  (conjunto&, conjunto&);
         friend ostream& operator << (ostream& out,conjunto& c);
         friend istream& operator >> (istream& in ,conjunto& c);
};

/*--------------------------------------------------------------------------*/

Boolean operator & (int elem, conjunto& conj)
/* verifica la pertenencia de un elemento en un conjunto regresando un valor
booleano correspondiente */
{
    for (int i = 0; i < conj.card; ++i)
        if (conj.elems[i] == elem) return TRUE;
    return FALSE;
}  /* operator & */

/*--------------------------------------------------------------------------*/

Boolean operator & (conjunto& conj, int elem )
/* verifica la pertenencia de un elemento en un conjunto regresando un valor
booleano correspondiente */
{
    for (int i = 0; i < conj.card; ++i)
        if (conj.elems[i] == elem) return TRUE;
    return FALSE;
}  /* operator & */

/*--------------------------------------------------------------------------*/

conjunto conjunto::operator = (int elem)
/* coloca un elemento en el conjunto destino */
{
    if ((!(elem & (*this))) && (card < MaxCard)) {
        this->elems[card] = elem;
        this->card++;
    }
    return *this;
}  /* operator = */

/*--------------------------------------------------------------------------*/

conjunto conjunto::operator = (conjunto& c)
/* copia un conjunto en otro */
{
    for (int i = 0; i < c.card; ++i)
        elems[i] = c.elems[i];
    card = c.card;
    return *this;
}  /* operator = */

/*--------------------------------------------------------------------------*/

Boolean operator == (conjunto& c1, conjunto& c2)
/* compara dos conjuntos, si son iguales regresa TRUE, si no, FALSE */
{
    if (c1.card != c2.card) return FALSE;
    for (int i = 0; i < c1.card; ++i)
        if (!(c1.elems[i] & c2)) return FALSE;
    return TRUE;
}  /* operator == */

/*--------------------------------------------------------------------------*/

Boolean operator <= (conjunto& c1, conjunto& c2)
/* subconjunto estricto */
{
    if (c1.card > c2.card) return FALSE;
    for (int i = 0; i < c1.card; ++i)
        if (!(c1.elems[i] & c2)) return FALSE;
    return TRUE;
}  /* operator <= */

/*--------------------------------------------------------------------------*/

conjunto operator + (conjunto& c1, conjunto& c2)
/* une dos conjuntos y regresa el resultado */
{
    conjunto res = c1;

    for (int i = 0; i < c2.card; ++i)
        res = c2.elems[i];
    return res;
}  /* operator + */

/*--------------------------------------------------------------------------*/

conjunto operator - (conjunto& c, int elem)
/* elimina un elemento de un conjunto y regresa el conjunto ampliado */
{
    for (int i = 0; i < c.card; ++i)
        if (c.elems[i] == elem) {
            for (; i < c.card-1; ++i)             // mover elems. a la izq.
                c.elems[i] = c.elems[i+1];
            --c.card;
        }
    return c;
}  /* operator - */

/*--------------------------------------------------------------------------*/

conjunto operator -  (conjunto& c1, conjunto& c2)
/* resta un conjunto de otro y regresa el resultado */
{
    conjunto res;

    for (int i = 0; i < c2.card; ++i)
        if (c1 & c2.elems[i])
            res = c1 - c2.elems[i];
    return res;
}  /* operator - */

/*--------------------------------------------------------------------------*/

conjunto operator * (conjunto& c1,conjunto& c2)
/* intersecta dos conjuntos y regresa el resultado */
{
    conjunto res;

    for (int i = 0; i < c1.card; ++i)
        if (c1.elems[i] & c2)
            res = c1.elems[i];
    return res;
}  /* operator * */

/*--------------------------------------------------------------------------*/

ostream& operator << (ostream& out,conjunto& c)
/* sobrecarga al operador de salida << para imprimir conjuntos */
{
    out << "{";
    for (int i = 0; i < c.card-1; ++i)
        out << c.elems[i] << ",";
    if (c.card > 0)
        out << c.elems[c.card-1];
    out << "}";
    return out;
}  /* oparator << */

/*--------------------------------------------------------------------------*/

istream& operator >> (istream& in,conjunto& c)
/*lee un conjunto con el formato tradicional de matem ticas: {e1,e2,...,eN} */
{
    int elem;
    char ch = ' ';
    Boolean comma = FALSE;

    c.card = 0;                                   // inicialmente c esta vac¡o
    in >> ch;
    if (ch == '{')
       for (;;) {
           in >> ch;
           switch (ch) {
               case '}': if (comma)
                             in.clear(1);                          // error
                         return in;
               case ',': if (comma || c.card == 0) {
                             in.clear(1);                          // error
                         return in;
                         }
                         comma = TRUE;
                         break;
               case ' ':                                    // ignorar blancos
               case '\t':
               case '\r': break;
               default: in.putback(ch);                 // eliminar: in >> ch;
                        in >> elem;
                        if (!in.good() || c.card > 0 && !comma) {
                            in.clear(1);                           // error
                            return in;
                        }
                        c = elem;
                        comma = FALSE;
                        break;
           }
       }
   return in;
}  /* operator >> */

/*--------------------------------------------------------------------------*/