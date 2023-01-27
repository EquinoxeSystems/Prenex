/****************************************************************************/
/*  Programa para convertir una F.B.F. del cálculo de predicados de primer  */
/*            orden a la Forma Normal PRENEX. Versión 3.2 (TC++)            */
/*                                                                          */
/*  Realizado por: Rodolfo González González.                               */
/****************************************************************************/

#include <stdlib.h>
#include <stdio.h>
#include <conio.h>
#include <string.h>
#include <ctype.h>
#include <alloc.h>
#include <values.h>
#include <dos.h>
#include <math.h>

#include <marcos.h>
#include "conjunto.h"

//----------------------------------------------------------------------------

#define NOERROR         0
#define NOBALANCE       1
#define NOSYMBOL        2
#define NOOPERS         3
#define VACIA           4
#define NOCONECT        5
#define NOVALIDPRED     6
#define DIFNUMTERMS     7
#define NOVALIDCUANT    8
#define NOVALIDVAR      9
#define NOVALIDSUBFFBF 10
#define NOVALIDFINAL   11
#define NOFNP          12
#define TERMINE   MAXINT

#define THEN   '>'
#define NOT    '~'
#define AND    '^'
#define OR     '#'
#define TODOS  '%'
#define EXISTE '?'

#define MAXFBF   500
#define MAXVAR   27
#define MAXCHECK 200

//----------------------------------------------------------------------------

char* errores[] = {
      "No hubo error",
      "Par‚ntesis no balanceados",
      "S¡mbolo desconocido",
      "Operandos incorrectos o incorrecto n£mero de operandos",
      "Parte de la 'FBF' de entrada esta vac¡a",
      "Error en los conectivos",
      "Predicado no v lido, sint xis incorrecta",
      "No concuerdan los n£meros de t‚rminos del mismo predicado",
      "Cuantificador no v lido, sint xis incorrecta",
      "Variable no v lida, sint xis incorrecta",
      "Iniciador de subFBF no v lido, sint xis incorrecta",
      "Terminador de subFBF no v lido, sint xis incorrecta",
      "FNP no v lida ya que no cumple el punto 3 de la definici¢n"
};

//----------------------------------------------------------------------------

typedef enum {FINAL,PREDICADO,VARIABLE,CUANTIFICADOR,CONECTIVA,subFBF,iniMATRIZ,finMATRIZ} TipoToken;

typedef struct tk {
           char      info[MAXFBF];
           TipoToken tipo;
           int       nivel;
           struct tk *sig, *ant;
        } Token;

typedef struct {
           int link;
           int num;
           int tipo;
           int nivel;
        } ligadas;

typedef struct {
           int  nargs;
           int  asign;
        } predicados;

typedef char cad20[20];

//----------------------------------------------------------------------------

conjunto conect;
conjunto cuanti;

int  variables[MAXVAR];
int  inc[MAXVAR];
ligadas ligada[MAXVAR];
predicados preds[MAXVAR];
cad20 varcuan[MAXCHECK];
cad20 varmatr[MAXCHECK];

char fbf[MAXFBF];

Token *primero=NULL, *ultimo=NULL, *anterior=NULL, *actual=NULL;
Token *ap=NULL;

int cambio = 0, reg = 0, e = NOERROR;

//----------------------------------------------------------------------------

void mensaje(char s[]);
void pausa(char s[]);

//----------------------------------------------------------------------------

void strshr(char s[], int p, int n)
// recorre a la derecha la cadena s n caracteres a partir del p-‚simo caracter
{
    for (int j=0; j<n; ++j) {
       for (int i=strlen(s); i>=p; --i)
          s[i+1] = s[i];
       s[p] = ' ';
    }
}

//----------------------------------------------------------------------------

void strclr(char s[])
/* elimina espacios en blanco de una cadena                                 */
{
    char aux[MAXFBF];
    int j=0;

    memset(aux,0,sizeof(aux));
    for (int i=0; i<strlen(s); i++)
       if (!isspace(s[i])) {
          aux[j] = s[i];
          j++;
       }
    memset(s,0,sizeof(s)); strcpy(s,aux);
}

//----------------------------------------------------------------------------

int par(int i)
// verifica si un n£mero es par, regresando 1 si lo es o 0 en otro caso
{
    if (fmod((double)i,2.0)==0) return 1;
    else return 0;
}

//----------------------------------------------------------------------------

int parentesis(char f[])
/* Verifica si los par‚ntesis de una expresi¢n estan bien balanceados       */
{
    int cuenta=0;

    for (int i=0; i<strlen(f); i++)
       if (f[i] == '(') cuenta++;
       else if (f[i] == ')') cuenta--;
    if (cuenta != 0) return NOBALANCE;
    return NOERROR;
}

//----------------------------------------------------------------------------

int simbolos(char fbf[])
/* Verifica los s¡mbolos de una expresi¢n para ver si son v lidos           */
{
    for (int i=0; i<strlen(fbf); i++)
       if ((!(fbf[i] & conect)) && (!(fbf[i] & cuanti)) && (fbf[i] != '(') &&
           (fbf[i] != ')') && (fbf[i] != ',') && (!isalpha(fbf[i])) && (!isspace(fbf[i])))
          return NOSYMBOL;
    return NOERROR;
}

//----------------------------------------------------------------------------

void guarda_token(char p[], TipoToken tip, int nivel)
/* Crea un nuevo nodo de una lista doblemente ligada                        */
{
   if (primero == NULL) {
      if ((actual = (Token*)farmalloc(sizeof(Token))) == NULL) {
         mensaje("Memoria agotada");
         exit(1);
      }
      strcpy(actual->info,p);
      actual->tipo   = tip;
      actual->nivel  = nivel;
      actual->sig    = NULL;
      actual->ant    = NULL;
      primero        = actual;
      ultimo         = actual;
   }
   else {
      anterior = ultimo;
      actual   = (Token*)malloc(sizeof(Token));
      strcpy(actual->info,p);
      actual->tipo   = tip;
      actual->nivel  = nivel;
      anterior->sig  = actual;
      actual->sig    = NULL;
      actual->ant    = anterior;
      ultimo         = actual;
   }
}

//----------------------------------------------------------------------------

int parse(char fbf[])
/* Obtiene una lista doblemente ligada con las partes de una FBF del c lculo*/
/* de predicados de primer orden, donde se entiende por partes a::          */
/* 1. Conectivos: ¢ (#), y (^), implicaciones (>), negaciones (~)           */
/* 2. Cuantificadores: universal ((%x)), existencial ((?x))                 */
/* 3. Predicados: P(x1,...,xN)                                              */
/* 4. Limitadores de subFBF's: '(' y ')'                                    */
{
    char aux[MAXFBF];
    int i = 0, j = 0, ya = 0, nivel = 0, cn = 0;
    TipoToken tip = FINAL;

    strclr(fbf);
    if (strcmp(fbf,"")==0) return VACIA;
    while (i < strlen(fbf)) {
       memset(aux,0,sizeof(aux));
       while ((fbf[i]!=')') && (i<strlen(fbf))) {
          if ((tip == PREDICADO) && (fbf[i] & conect)) {
             cn = 1; break;
          }
          if ((tip==CUANTIFICADOR) && (isalpha(fbf[i])) && (j>0))
             fbf[i] = tolower(fbf[i]);
          if ((fbf[i]=='(') && (isalpha(fbf[i+1])) && (fbf[i+2]=='('))
             fbf[i+1] = toupper(fbf[i+1]);
          if (((fbf[i]>='a') && (fbf[i]<='z')) && ((fbf[i+1]=='(')))
             fbf[i] = toupper(fbf[i]);
          aux[j] = fbf[i];
          if ((tip==PREDICADO) && (isalpha(fbf[i+1])) && (j>0))
             fbf[i+1] = tolower(fbf[i+1]);
          if ((fbf[i] == '(') && ((fbf[i+1] != TODOS) && (fbf[i+1] != EXISTE) &&
              ((fbf[i+1] < 'a') || (fbf[i+1] > 'z')))) {
             nivel++; tip = subFBF; break;
          }
          if (!ya)
             if (fbf[i] & conect) { tip = CONECTIVA; ya = 1; break; }
             else
                if ((fbf[i] >= 'A') && (fbf[i] <= 'Z')) { tip = PREDICADO; ya = 1; }
                else
                   if ((fbf[i] >= 'a') && (fbf[i] <= 'z')) { tip = VARIABLE; ya = 1; }
                   else
                      if (fbf[i] & cuanti) { tip = CUANTIFICADOR; ya = 1; }
          i++; j++;
       }
       if (!cn) aux[j++] = fbf[i++];
       guarda_token(aux,tip,nivel);
       if (tip == FINAL) nivel--;
       ya = j = cn = 0; tip = FINAL;
    }
    return NOERROR;
}

//----------------------------------------------------------------------------

int binarios(Token *fbf)
/* verifica la sint xis de los operadores binarios ^, #, >, verificando que */
/* tengan 2 operadores                                                      */
{
    Token *p;

    while (fbf!=NULL) {
       if ((strcmp(fbf->info,">") == 0) || (strcmp(fbf->info,"^") == 0) ||
           (strcmp(fbf->info,"#") == 0)) {
          if (fbf->ant == NULL)
             return NOOPERS;
          if ((fbf->ant->tipo == PREDICADO) || (fbf->ant->tipo == FINAL)) {
             p = fbf->sig;
             while ((p->tipo == CUANTIFICADOR) || (strcmpi(p->info,"~") == 0))
                p = p->sig;
             if ((p->tipo != PREDICADO) && (p->tipo != subFBF))
                return NOOPERS;
          }
          else return NOOPERS;
       }
       fbf = fbf->sig;
    }
    return NOERROR;
}

//----------------------------------------------------------------------------

int unarios(Token *fbf)
/* verifica la sint xis del operador ~                                      */
{
    while (fbf != NULL) {
       if (strcmpi(fbf->info,"~") == 0) {
          if (((fbf->ant->tipo == PREDICADO) || (fbf->ant->tipo == FINAL))
             && (fbf->ant != NULL))
             return NOOPERS;
       }
       fbf = fbf->sig;
    }
    return NOERROR;
}

//----------------------------------------------------------------------------

int general(Token *fbf)
// verifica la sint xis general de la fbf, subFBF's no vac¡as, o sin conectivo
{
    Token *p;

    while (fbf != NULL) {
       if (fbf->tipo == subFBF) {
          p = fbf->sig;
          while ((p->tipo == subFBF) && (p != NULL)) p = p->sig;
          if (p->tipo == FINAL)
             return VACIA;
       }
       if (fbf->tipo == FINAL) {
          p = fbf->sig;
          while ((p->tipo == FINAL) && (p != NULL)) p = p->sig;
          if ((p->tipo != CONECTIVA) && (p != NULL))
             return NOCONECT;
        }
       fbf = fbf->sig;
    }
    return NOERROR;
}

//----------------------------------------------------------------------------

int checanum(char f[])
// regresa el n£mero de variables individuales que son t‚rminos de un
// predicado
{
    int cuenta = 0;

    for (int i=0; i<strlen(f); i++) {
       if ((f[i]>='a') && (f[i]<='z')) cuenta++;
    }
    return cuenta;
}

//----------------------------------------------------------------------------

int particular (Token *fbf)
// verifica la sint xis paticular de cada parte de la fbf
{
    while (fbf!=NULL) {
       if (fbf->tipo==PREDICADO) {
          if (strlen(fbf->info)>1) {
             if ((fbf->info[0] >= 'A') && (fbf->info[0] <= 'Z') &&
                 (fbf->info[1]=='(') && (isalpha(fbf->info[2]))) {
                if (preds[fbf->info[0]-'A'].asign) {
                   if (checanum(fbf->info) != preds[fbf->info[0]-'A'].nargs)
                      return DIFNUMTERMS;
                }
                else {
                   preds[fbf->info[0]-'A'].asign = 1;
                   preds[fbf->info[0]-'A'].nargs = checanum(fbf->info);
                }
                if (strlen(fbf->info)>1) {
                   for (int i=2; i<strlen(fbf->info)-1; i++)
                      if (par(i)) {
                         if (!isalpha(fbf->info[i])) return NOVALIDPRED;
                      }
                      else
                         if (fbf->info[i]!=',') return NOVALIDPRED;
                      if (fbf->info[i++]!=')') return NOVALIDPRED;
                }
             }
             else return NOVALIDPRED;
          }
          else
             if (!isalpha(fbf->info[0])) return NOVALIDPRED;
       }
       else
          if (fbf->tipo==CUANTIFICADOR) {
             if ((fbf->info[0]!='(') || !(fbf->info[1]&cuanti) ||
                 !(isalpha(fbf->info[2])) || (fbf->info[3]!=')'))
                return NOVALIDCUANT;
          }
          else
             if ((fbf->tipo==VARIABLE) && (strlen(fbf->info)!=1))
                return NOVALIDVAR;
             else
                if ((fbf->tipo==subFBF) && (strcmp(fbf->info,"(")!=0))
                   return NOVALIDSUBFFBF;
                else
                   if ((fbf->tipo==FINAL) && (strcmp(fbf->info,")")!=0))
                      return NOVALIDFINAL;
       fbf = fbf->sig;
    }
    return NOERROR;
}

//----------------------------------------------------------------------------

void negaciones(Token *fbf)
/* Cambia subFBF's ~(?x)A(x) por (%x)~A(x), y ~(%x)A(x) por (?x)~A(x)       */
{
    char aux[10];

    memset(aux,0,sizeof(aux));
    while (fbf != NULL) {
       if ((fbf->tipo == CONECTIVA) && (strcmpi(fbf->info,"~") == 0))
          if (fbf->sig->tipo == CUANTIFICADOR) {
             fbf->sig->tipo = CONECTIVA;
             fbf->tipo = CUANTIFICADOR;
             strcpy(aux,fbf->sig->info);
             strcpy(fbf->sig->info,"~");
             strcpy(fbf->info,aux);
             if (strncmpi(fbf->info,"(%",2) == 0)
                fbf->info[1] = EXISTE;
             else
                if (strncmpi(fbf->info,"(?",2) == 0)
                   fbf->info[1] = TODOS;
             cambio = 1;
          }
       fbf = fbf->sig;
    }
}

//----------------------------------------------------------------------------

void conjunciones(Token **fbf)
/* Cambia subFBF's de la forma (p^q) por ~(p>~q)                            */
{
    char aux[10];
    Token *niega_cons, *abre_par, *niega_todo, *cierra_par, *p;
    int niv_act, niv_ant;

    /* buscar p^q */
    memset(aux,0,sizeof(aux));
    while ((*fbf) != NULL) {
       if (((*fbf)->tipo == CONECTIVA) && (strcmpi((*fbf)->info,"^") == 0)) {
          /* inicializar sustituidores */
          if ((niega_todo = (Token*)farmalloc(sizeof(Token))) == NULL) {
             mensaje("Memoria agotada");
             exit(1);
          }
          strcpy(niega_todo->info,"~"); niega_todo->tipo = CONECTIVA; niega_todo->nivel = (*fbf)->ant->nivel;
          if ((abre_par = (Token*)farmalloc(sizeof(Token))) == NULL) {
             mensaje("Memoria agotada");
             exit(1);
          }
          strcpy(abre_par->info,"("); abre_par->tipo = subFBF; abre_par->nivel = (*fbf)->ant->nivel;
          if ((niega_cons = (Token*)farmalloc(sizeof(Token))) == NULL) {
             mensaje("Memoria agotada");
             exit(1);
          }
          strcpy(niega_cons->info,"~"); niega_cons->tipo = CONECTIVA; niega_cons->nivel = (*fbf)->sig->nivel;
          if ((cierra_par = (Token*)farmalloc(sizeof(Token))) == NULL) {
             mensaje("Memoria agotada");
             exit(1);
          }
          strcpy(cierra_par->info,")"); cierra_par->tipo = FINAL; cierra_par->nivel = (*fbf)->sig->nivel;

          /* sustituir ^ por > */
          memset((*fbf)->info,0,sizeof((*fbf)->info)); strcpy((*fbf)->info,">");

          /* negar consecuente, para obtener p>~q */
          p = *fbf;
          niega_cons->sig = p->sig; p->sig->ant = niega_cons;
          p->sig = niega_cons; niega_cons->ant = p;

          /* obtener n£mero de niveles actual y anterior */
          niv_act = (*fbf)->nivel;
          niv_ant = (*fbf)->ant->nivel;

          /* negar todo, para obtener ~(p>~q */
          p = *fbf;
          if (p->ant->tipo==FINAL)
             while ((p->ant!=NULL) && (p->ant->nivel==niv_ant) &&
                    ((p->tipo!=subFBF) || (p->ant->tipo!=CONECTIVA) ||
                     (strcmpi(p->ant->info,"~")==0))) p = p->ant;
          else
             while ((p->ant!=NULL) && (p->nivel==niv_act) &&
                    ((p->tipo!=subFBF) && (p->ant->tipo!=CONECTIVA) ||
                     (strcmpi(p->ant->info,"~")==0))) p = p->ant;
          while ((p->ant!=NULL) &&
                ((p->ant->tipo==CUANTIFICADOR) || (strcmpi(p->ant->info,"~")==0 )))
                p = p->ant;

          niega_todo->sig = abre_par; abre_par->ant = niega_todo;
          niega_todo->ant = p->ant;
          if (p->ant!=NULL) p->ant->sig = niega_todo;
          abre_par->sig = p; p->ant = abre_par;

          /* cerrar par‚ntesis al final de todo, para obtener ~(p>~q) */
          p = *fbf;
          while (p->tipo == CONECTIVA) p = p->sig;
          if (p->tipo==subFBF)
             while ((p->sig!=NULL) && (p->nivel!=niv_act)) p = p->sig;
          else
             while ((p->sig!=NULL) && (p->sig->nivel==niv_act)) p = p->sig;

          if (p->sig != NULL) p->sig->ant = cierra_par;
          cierra_par->sig = p->sig; p->sig = cierra_par;
          cierra_par->ant = p;

          cambio = 1;
          break;
       }
       *fbf = (*fbf)->sig;
    }
}

//----------------------------------------------------------------------------

void disyunciones(Token **fbf)
/* Cambia subFBF's de la forma (p#q) por (~p>q)                             */
{
    char aux[10];
    Token *niega_ante, *p;
    int niv_act, niv_ant;

    memset(aux,0,sizeof(aux));
    while ((*fbf) != NULL) {
       if (((*fbf)->tipo == CONECTIVA) && (strcmpi((*fbf)->info,"#") == 0)) {
          /* inicializa substituidor */
          if ((niega_ante = (Token*)farmalloc(sizeof(Token))) == NULL) {
             mensaje("Memoria agotada");
             exit(1);
          }
          strcpy(niega_ante->info,"~"); niega_ante->tipo = CONECTIVA; niega_ante->nivel = (*fbf)->ant->nivel;

          /* sustituir # por > */
          memset((*fbf)->info,0,sizeof((*fbf)->info)); strcpy((*fbf)->info,">");

          /* obtener n£mero de niveles actual y anterior */
          niv_act = (*fbf)->nivel;
          niv_ant = (*fbf)->ant->nivel;

          /* negar todo, para obtener ~p>q */
          p = *fbf;
          if (p->ant->tipo==FINAL)
             while ((p->ant!=NULL) && (p->ant->nivel==niv_ant) &&
                    ((p->tipo!=subFBF) || (p->ant->tipo!=CONECTIVA) ||
                     (strcmpi(p->ant->info,"~")==0))) p = p->ant;
          else
             while ((p->ant!=NULL) && (p->nivel==niv_act) &&
                    ((p->ant->tipo!=subFBF) && (p->ant->tipo!=CONECTIVA) ||
                     (strcmpi(p->ant->info,"~")==0))) p = p->ant;
          while ((p->ant!=NULL) &&
                ((p->ant->tipo==CUANTIFICADOR) || (strcmpi(p->ant->info,"~")==0 )))
                p = p->ant;

          niega_ante->ant = p->ant;
          if (p->ant!=NULL) p->ant->sig = niega_ante;
          niega_ante->sig = p; p->ant = niega_ante;

          cambio = 1;
          break;
       }
       *fbf = (*fbf)->sig;
    }
}

//----------------------------------------------------------------------------

void re_nivela1(Token **fbf)
// coloca los n£meros de anidamiento de par‚ntesis correctamente
{
    int nivel = 0;

    while (*fbf != NULL) {
       if ((*fbf)->tipo == subFBF) nivel++;
       else if (((*fbf)->tipo == FINAL) && (nivel-1 >= 0)) nivel--;
       (*fbf)->nivel = nivel; *fbf = (*fbf)->sig;
    }
}

//----------------------------------------------------------------------------

void re_nivela2(Token **fbf)
{
    int nivel = -MAXINT;

    while ((*fbf)->tipo!=iniMATRIZ) {
       (*fbf)->nivel = nivel; *fbf = (*fbf)->sig;
    }
    (*fbf)->nivel = nivel; *fbf = (*fbf)->sig; nivel = 0;
    re_nivela1(&(*fbf));
}

//----------------------------------------------------------------------------

void instancia_predicados(Token **fbf)
// instancia las variables de una predicado
{
    char aux[10];

    memset(aux,0,sizeof(aux));
    for (int i=2; i<strlen((*fbf)->info); ++i) {
        if ((((*fbf)->info[i] >= 'a') && ((*fbf)->info[i] <= 'z')) &&
            (((*fbf)->info[i+1] == ',') || ((*fbf)->info[i+1] == ')'))) {
           if ((variables[(*fbf)->info[i]-'a'] < 0) &&
               (!ligada[(*fbf)->info[i]-'a'].link)) {
              variables[(*fbf)->info[i]-'a']++;
              inc[(*fbf)->info[i]-'a'] = 1;
           }
           if (!ligada[(*fbf)->info[i]-'a'].link) {
              if ((!inc[(*fbf)->info[i]-'a']) && (!ligada[(*fbf)->info[i]-'a'].link)) {
                 variables[(*fbf)->info[i]-'a']++;
                 inc[(*fbf)->info[i]-'a'] = 1;
              }
              if (variables[(*fbf)->info[i]-'a'] < 0) variables[(*fbf)->info[i]-'a']++;
              strshr((*fbf)->info,i+1,strlen(itoa(variables[(*fbf)->info[i]-'a'],aux,10)));
              memcpy(&((*fbf)->info[i+1]),aux,strlen(aux));
              memset(aux,0,sizeof(aux));
           }
           else {
              if (ligada[(*fbf)->info[i]-'a'].num < 0) ligada[(*fbf)->info[i]-'a'].num++;
              strshr((*fbf)->info,i+1,strlen(itoa(ligada[(*fbf)->info[i]-'a'].num,aux,10)));
              memcpy(&((*fbf)->info[i+1]),aux,strlen(aux));
              memset(aux,0,sizeof(aux));
           }
        }
    }
}

//----------------------------------------------------------------------------

void sustituciones(Token **fbf)
// instancia variables dentro de una fbf del c lculo de predicados de primer
// orden.
{
    Token *p = NULL;
    char aux[10];

    memset(aux,0,sizeof(aux));
    while (*fbf != NULL) {
       if ((*fbf)->tipo == CUANTIFICADOR) {
          p = (*fbf)->sig;
          while (strcmpi(p->info,"~") == 0) p = p->sig;
          if ((*fbf)->info[3] == ')') {
             variables[(*fbf)->info[2]-'a']++;
             ligada[(*fbf)->info[2]-'a'].link  = 1;
             ligada[(*fbf)->info[2]-'a'].nivel = (*fbf)->nivel;
             ligada[(*fbf)->info[2]-'a'].num = variables[(*fbf)->info[2]-'a'];
             if (p->tipo == PREDICADO) ligada[(*fbf)->info[2]-'a'].tipo = 0;
             if (p->tipo == subFBF) ligada[(*fbf)->info[2]-'a'].tipo = 1;
             strshr((*fbf)->info,3,strlen(itoa(variables[(*fbf)->info[2]-'a'],aux,10)));
             memcpy(&((*fbf)->info[3]),aux,strlen(aux));
             memset(aux,0,sizeof(aux));
          }
          if (p->tipo == PREDICADO) {
             instancia_predicados(&p);
             for (int i=0; i<MAXVAR; i++) {
                if ((ligada[i].link) && (ligada[i].tipo==1)) ligada[i].num--;
                if ((ligada[i].link) && (ligada[i].tipo==0)) ligada[i].link=0;
             }
          }
          if (p->tipo == subFBF) sustituciones(&p);
       }
       if ((*fbf)->tipo == PREDICADO) {
          memset(inc,0,sizeof(inc)); instancia_predicados(&(*fbf));
       }
       if ((*fbf)->tipo == FINAL) {
          for (int i=0; i<MAXVAR; i++) {
             if ((ligada[i].nivel == (*fbf)->nivel) && (ligada[i].link))
                ligada[i].nivel = ligada[i].num = -1; ligada[i].link = 0;
          }
       }
       *fbf = (*fbf)->sig;
    }
}

//----------------------------------------------------------------------------

void pon_corchetes(void)
// coloca los corchetes alrededor de la matr¡z
{
    Token *abre;

    while (ultimo->sig != NULL) ultimo = ultimo->sig;
    if ((abre = (Token*)farmalloc(sizeof(Token))) == NULL) {
       mensaje("Memoria agotada");
       exit(1);
    }
    if ((ultimo->sig = (Token*)farmalloc(sizeof(Token))) == NULL) {
       mensaje("Memoria agotada");
       exit(1);
    }
    strcpy(abre->info,"["); strcpy(ultimo->sig->info,"]");
    abre->nivel = ultimo->sig->nivel = -MAXINT;
    abre->tipo = iniMATRIZ; ultimo->sig->tipo = finMATRIZ;
    abre->ant = ultimo->sig->sig = NULL;
    abre->sig = primero; primero->ant = abre; primero = abre;
    ultimo->sig->ant = ultimo;
}

//----------------------------------------------------------------------------

void saca_cuantificadores(Token **fbf)
// saca los cuantificadores existenciales y univesales, formando la matriz y
// el prefijo.
{
    Token *p;
    int niv_act, si=1;

    while ((*fbf != NULL) && ((*fbf)->tipo != finMATRIZ)) {
       if (((*fbf)->tipo == CUANTIFICADOR) && ((*fbf)->nivel != -MAXINT)) {
          if (((*fbf)->ant->tipo==subFBF) || ((*fbf)->ant->tipo==iniMATRIZ)){
             /* cambiar (?x)A(x)>B por (%x)(A(x)>B) y (%x)A(x)>B por (?x)(A(x)>B) */
             if ((*fbf)->ant->tipo==iniMATRIZ) {
                p = *fbf;
                while ((p->tipo==CUANTIFICADOR) || (strcmp(p->info,"~")==0)
                       && (p->sig!=NULL)) p = p->sig;
                if (p->tipo==subFBF) {
                   niv_act = p->nivel; p = p->sig;
                   while ((p->nivel>=niv_act) && (p->sig->tipo!=finMATRIZ)) p = p->sig;
                   if (p->sig->tipo==finMATRIZ) si = 0;
                   else {
                      while ((p->tipo==FINAL) && (p->sig->tipo!=finMATRIZ)) p = p->sig;
                      if (p->sig->tipo==finMATRIZ) si = 0;
                      else si = 1;
                   }
                }
                else if (p->tipo==PREDICADO) si = 1;
             }
             if (si)
                if ((*fbf)->info[1] == '%') (*fbf)->info[1] = '?';
                else if ((*fbf)->info[1] == '?') (*fbf)->info[1] = '%';
             p = *fbf; p->nivel = p->ant->nivel;
             p->ant->sig = p->sig; p->sig->ant = p->ant; p->sig = p->ant;
             p->ant = p->ant->ant; p->ant->sig = p; p->sig->ant = p;
             cambio = 1;
             break;
          }
          else if (strcmpi((*fbf)->ant->info,">")==0) {
                  /* cambiar A>(%x)B(x) por (%x)(A>B(x)) y A>(?x)B(x) por (?x)(A>B(x)) */
                  p = (*fbf)->ant->ant->ant; niv_act = (*fbf)->ant->ant->nivel;
                  while ((p->nivel != niv_act) && (p->tipo!=iniMATRIZ)) p = p->ant;
                  while (strcmpi(p->info,"~")==0) p = p->sig;
                  (*fbf)->ant->sig = (*fbf)->sig;
                  (*fbf)->sig->ant = (*fbf)->ant;
                  (*fbf)->sig = p;
                  (*fbf)->ant = p->ant;
                  p->ant->sig = *fbf;
                  p->ant = *fbf;
                  cambio = 1;
                  break;
               }
       }
       *fbf = (*fbf)->sig;
    }
}

//----------------------------------------------------------------------------

int esta(cad20 var, cad20 lis[])
{
    for (int i=0; i<MAXCHECK; i++) {
       if (strcmp(var,lis[i])==0) return 1;
    }
    return 0;
}

//----------------------------------------------------------------------------

int checa_validez(Token *fnp)
// verifica que todas las variables xi del prefijo de la fnp est‚n en la
// matr¡z de la fnp, seg£n la definici¢n.
{
    int cuenta=0, j=0;
    cad20 aux;

    memset(aux,0,sizeof(aux));
    while (fnp->tipo!=iniMATRIZ) {
       // hallar que variables individuales estan presentes en el prefijo
       for (int i=2; i<strlen(fnp->info)-1; i++) {
          if (isalpha(fnp->info[i])) {
             aux[j] = fnp->info[i]; j++; i++;
             while (isdigit(fnp->info[i])) {
                aux[j] = fnp->info[i]; j++; i++;
             }
             strcpy(varcuan[cuenta],aux); cuenta++; j=0;
             memset(aux,0,sizeof(aux));
          }
       }
       fnp = fnp->sig;
    }
    cuenta=0; j=0;
    while (fnp->tipo!=finMATRIZ) {
       // verificar que todas las variables presentes en los cuantificadores
       // del prefijo est‚n en la parte de la matr¡z de la fnp
       if (fnp->tipo==PREDICADO) {
          for (int i=2; i<strlen(fnp->info)-1; i++) {
             if (isalpha(fnp->info[i])) {
                aux[j] = fnp->info[i]; j++; i++;
                while (isdigit(fnp->info[i])) {
                   aux[j] = fnp->info[i]; j++; i++;
                }
                strcpy(varmatr[cuenta],aux); cuenta++; j=0;
                memset(aux,0,sizeof(aux));
             }
          }
       }
       fnp = fnp->sig;
    }
    for (int i=0; i<MAXCHECK; i++)
       if (!esta(varcuan[i],varmatr)) return NOFNP;
    return NOERROR;
}

//----------------------------------------------------------------------------

void imprime_fbf(Token *ap)
/* Imprime la FBF almacenada en la lista ligada de an lisis                 */
{
    if (wherey()==15) {
       pausa("Presione una tecla para ver la siguiente pantalla de resultados..."); window(3,8,77,22); textcolor(LIGHTGREEN);
       textbackground(LIGHTBLUE); clrscr();
    }
    while (ap != NULL) {
       cprintf("%s",ap->info);
       ap = ap->sig;
    }
    cprintf("\n\r");
}

//----------------------------------------------------------------------------

void rewind(void)
/* Coloca el apuntador "primero" al inicio de la lista                      */
{
    while (primero->ant != NULL) primero = primero->ant;
}

//----------------------------------------------------------------------------

void DestruyeLista(Token **lista)
/* libera la memoria ocupada por la lista de trabajo                        */
{
    Token *temp;

    if (*lista != NULL) {
        DestruyeLista(&(*lista)->sig);
        temp = *lista;
        temp->sig = NULL;
        farfree(*lista);
    }
}

//----------------------------------------------------------------------------

void inicializa()
/* inicializa variables globales                                            */
{
    DestruyeLista(&primero);
    primero = ultimo = anterior = actual = ap = NULL;
    e = cambio = reg = 0;
    memset(variables,-1,sizeof(variables));
    memset(inc,0,sizeof(inc));
    for (int i=0; i<MAXVAR; ++i) {
       ligada[i].link = ligada[i].num = 0;
       ligada[i].nivel = ligada[i].tipo = -1;
    }
    memset(preds,0,sizeof(preds));
    memset(fbf,0,sizeof(fbf));
    memset(varcuan,0,sizeof(fbf));
    memset(varmatr,0,sizeof(fbf));
}

//----------------------------------------------------------------------------

void mensaje(char s[])
// escribe un mensaje de error
{
    int x1 = (80 - strlen(s)) / 2;
    int x2 = (x1+1+strlen(s));

    _setcursortype(_NOCURSOR);
    sound(1000); delay(150); nosound(); window(1,1,80,25);
    marco(x1-1,19,x2-1,21,YELLOW,LIGHTRED,SENCILLO);
    textcolor(YELLOW); textbackground(LIGHTRED);
    gotoxy(x1,20); cprintf("%s",s);
    while(kbhit()) getch(); while(!kbhit()); while(kbhit()) getch();
    _setcursortype(_NORMALCURSOR);
}

//----------------------------------------------------------------------------

int LeerFBF(void)
// lee una FBF de la consola
{
     char cad[MAXFBF+2];

     window(1,1,80,25); textbackground(BLACK); clrscr();
	 textcolor(BLACK); textbackground(WHITE); clrscr();
	 textbackground(BLACK); window(4,4,78,6); clrscr();
	 window(3,12,79,14); clrscr(); window(1,1,80,25);
	 marco(1,1,80,24,BLACK,LIGHTGRAY,DOBLE);
	 marco(3,3,77, 5,WHITE,LIGHTBLUE,DOBLE);
	 marco(2,11,78,13,WHITE,LIGHTBLUE,SENCILLO);
	 textcolor(WHITE); textbackground(LIGHTBLUE);
	 gotoxy(31, 4); textcolor(WHITE); textbackground(LIGHTBLUE);
	 window(4,4,76,4); clrscr(); gotoxy(13,1);
     cprintf("Escriba la FBF a convertir (ENTER para terminar)");
     window(3,12,77,12); clrscr(); textcolor(LIGHTGREEN); _setcursortype(_SOLIDCURSOR);
     cad[0] = MAXFBF; cgets(cad);
     if (cad[1]==0) return TERMINE;
     memcpy(fbf,&cad[2],cad[1]); _setcursortype(_NORMALCURSOR);
     return 0;
}

//----------------------------------------------------------------------------

void display()
// pone la ventana para desplegar el proceso de transformaci¢n
{
     window(1,1,80,25); textbackground(BLACK); textcolor(LIGHTGRAY); clrscr();
	 textcolor(BLACK); textbackground(WHITE); clrscr(); textbackground(BLACK);
     window(4,4,78,6); clrscr(); window(3,8,79,24); clrscr(); window(1,1,80,25);
     marco(3,3,77, 5,WHITE,LIGHTBLUE,DOBLE);
     marco(2,7,78,23,WHITE,LIGHTBLUE,DOBLE);
     textcolor(WHITE); textbackground(LIGHTBLUE); window(4,4,76,4); clrscr();
     gotoxy(16,1); cprintf("Convirtiendo a Forma Normal PRENEX...");
     textcolor(LIGHTGREEN); window(3,8,77,22); clrscr();
     _setcursortype(_NOCURSOR);
}

//----------------------------------------------------------------------------

void forma_comparativa(void)
// presenta la FBF original y la FNP resultante
{
     Token *p = primero;

     window(1,1,80,25); textbackground(BLACK); clrscr();
	 textcolor(BLACK); textbackground(WHITE); clrscr();
	 textbackground(BLACK); window(4,4,78,6); clrscr();
	 window(3,12,79,14); clrscr(); 	 window(3,17,79,19); clrscr();
     window(1,1,80,25);
	 marco(1,1,80,24,BLACK,LIGHTGRAY,DOBLE);
	 marco(3,3,77, 5,WHITE,LIGHTBLUE,DOBLE);
	 marco(2,11,78,13,WHITE,LIGHTBLUE,SENCILLO);
     marco(2,16,78,18,WHITE,LIGHTBLUE,SENCILLO);
	 textcolor(WHITE); textbackground(LIGHTBLUE);
	 gotoxy(31, 4); textcolor(WHITE); textbackground(LIGHTBLUE);
	 window(4,4,76,4); clrscr(); gotoxy(13,1);
     cprintf("FBF original (arriba) y FNP resultante (abajo)");
     window(3,12,77,12); clrscr(); textcolor(LIGHTGREEN); _setcursortype(_NOCURSOR);
     cprintf("%s",fbf);  window(3,17,77,17); clrscr(); textcolor(YELLOW);
     while (p != NULL) {
        cprintf("%s",p->info); p = p->sig;
     }
     pausa("Presione una tecla para regresar a la pantalla principal...");
}

//----------------------------------------------------------------------------

void pausa(char s[])
// hace una pausa hasta que se presione una tecla
{
    int x = (80 - strlen(s)) / 2;

    window(1,1,80,25); _setcursortype(_NOCURSOR);
    gotoxy(x,25); textcolor(LIGHTRED+BLINK); textbackground(LIGHTGRAY);
    cprintf("%s",s);
    while(kbhit()) getch(); while(!kbhit()); while(kbhit()) getch();
    gotoxy(x-1,25); clreol(); _setcursortype(_NORMALCURSOR);
}

//----------------------------------------------------------------------------

void portada(void)
// pone la portada del programa
{
    sound(392); delay(100); sound(523); delay(75); nosound();
    window(1,1,80,25); textcolor(BLACK); textbackground(LIGHTBLUE);
    clrscr(); textbackground(BLACK); window(15,7,67,16); clrscr(); window(1,1,80,25);
    marco(1,1,80,24,WHITE,LIGHTBLUE,DOBLE);  textbackground(LIGHTCYAN);
    marco(14,6,66,15,WHITE,LIGHTCYAN,DOBLE); window(15,7,65,14); clrscr(); window(1,1,80,25);
    gotoxy(15, 7); cprintf(" Programa para convertir una F.B.F. del c lculo de ");
    gotoxy(15, 8); cprintf("predicados de primer orden a la Forma Normal PRENEX");
    gotoxy(15,12); cprintf("     Realizado por:  Rodolfo Gonz lez Gonz lez     ");
    pausa("Presione cualquier tecla para continuar...");
}

//-------------------------- Programa Principal ------------------------------

int main(void)
{
    conect = THEN; conect = NOT; conect = AND; conect = OR;
    cuanti = TODOS; cuanti = EXISTE;
    portada();
    do {
       inicializa();
       if ((reg=LeerFBF()) != TERMINE) {
          display();
          if ((e=parentesis(fbf)) != NOERROR)
             mensaje(errores[e]);
          else {
             cprintf("Par‚ntesis balanceados\n\r");
             if ((e=simbolos(fbf)) != NOERROR)
                mensaje(errores[e]);
             else {
                cprintf("S¡mbolos correctos\n\r");
                if ((e=parse(fbf)) != NOERROR)
                   mensaje(errores[e]);
                else {
                   cprintf("Parsing completado\n\r");
                   if ((e=binarios(primero)) != NOERROR)
                      mensaje(errores[e]);
                   else {
                      cprintf("Operadores binarios correctos\n\r");
                      if ((e=unarios(primero)) != NOERROR)
                         mensaje(errores[e]);
                      else {
                         cprintf("Operadores unarios correctos\n\r");
                         if ((e=general(primero)) != NOERROR)
                            mensaje(errores[e]);
                         else {
                            cprintf("Sint xis general correcta\n\r");
                            if ((e=particular(primero)) != NOERROR)
                               mensaje(errores[e]);
                            else {
                               cprintf("Sint xis particular de los predicados y cuantificadores correcta\n\r");
                               do {
                                  cambio = 0; re_nivela1(&ap); rewind();
                                  ap = primero; imprime_fbf(ap);
                                  negaciones(ap);
                                  rewind(); ap = primero; imprime_fbf(ap);
                                  conjunciones(&ap);
                                  rewind(); ap = primero; imprime_fbf(ap);
                                  disyunciones(&ap);
                                  rewind();
                               } while (cambio);
                               ap = primero; re_nivela1(&ap); rewind();
                               imprime_fbf(ap); ap = primero;
                               sustituciones(&ap);
                               rewind(); ap = primero; imprime_fbf(ap);
                               pon_corchetes();
                               rewind(); ap = primero; imprime_fbf(ap);
                               do {
                                  cambio = 0; re_nivela2(&ap); rewind();
                                  ap = primero; imprime_fbf(ap);
                                  negaciones(ap);
                                  rewind(); ap = primero; imprime_fbf(ap);
                                  saca_cuantificadores(&ap);
                                  rewind(); ap = primero; imprime_fbf(ap);
                               } while (cambio);
                            }
                         }
                      }
                   }
                }
             }
          }
       }
       if ((e==NOERROR) && (reg != TERMINE)) {
          if ((e=checa_validez(primero))!=NOERROR) {
             mensaje(errores[e]);
          }
          else {
             cprintf("\n\rSe ha llegado a la F.N.P.!");
          }
       }
       if ((reg != TERMINE) && (e == NOERROR)) {
          pausa("Presione cualquier tecla para ver la FBF inicial y la FNP...");
          forma_comparativa();
       }
    } while (reg != TERMINE);
    window(1,1,80,25); textcolor(LIGHTGRAY); textbackground(BLACK); clrscr();
    _setcursortype(_NORMALCURSOR);
    return 0;
}
// fin del archivo principal