#include <conio.h>

#define SENCILLO 1
#define DOBLE 2

void marco (int x1,int y1,int x2,int y2,int c1,int c2,int Clase);

void marco (int x1,int y1,int x2,int y2,int c1,int c2,int Clase)
{
   struct text_info ti;
   int h,v,si,ii,sd,id,i;
   gettextinfo (&ti);
   textcolor (c1); textbackground (c2);
   switch (Clase) {
      case SENCILLO: {
                 h = 'Ä'; v = '³'; si = 'Ú'; ii = 'À'; sd = '¿'; id = 'Ù';
                 break;
      }
      case DOBLE: {
                 h = 'Í'; v = 'º'; si = 'É'; ii = 'È'; sd = '»'; id = '¼';
                 break;
      }
   }
   for (i = x1; i <= x2; i++) {gotoxy (i,y1); cprintf ("%c",h); }
   for (i = x1; i <= x2; i++) {gotoxy (i,y2); cprintf ("%c",h); }
   for (i = y1; i <= y2; i++) {gotoxy (x1,i); cprintf ("%c",v); }
   for (i = y1; i <= y2; i++) {gotoxy (x2,i); cprintf ("%c",v); }
   gotoxy (x1,y1); cprintf ("%c",si);
   gotoxy (x1,y2); cprintf ("%c",ii);
   gotoxy (x2,y1); cprintf ("%c",sd);
   gotoxy (x2,y2); cprintf ("%c",id);
   textattr (ti.attribute);
}




