/*
 * $Id: ike.c,v 1.26 2006/05/26 05:48:54 ikh Exp $
 *
 * Copyright (c) 2003-2005 Igor Khomyakov. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1) Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following disclaimer.
 * 2) Redistributions of source code with modification must include a notice
 * that the code was modified.
 * 3) Neither the names of the authors nor the names of their contributors may
 * be used to endorse or promote products derived from this software without
 * specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define PAGESZ  (1024*8)   /*in bytes --- page size */
#define WORDSZ  4          /*in bytes --- word size */
#define STRBSZ  PAGESZ     /*bytes --- temporary string buffer size */
#define SYMWSZ  8          /*words --- maximum symbol size in words including \0 */
#define SYMBSZ  (SYMWSZ*WORDSZ) /*bytes --- maximum symbol size including \0 */
#define DICTSZ  (PAGESZ/WORDSZ*8) /*words --- dictionary size*/
#define DATSSZ  (PAGESZ/WORDSZ*1)    /*words --- data stack size*/
#define RETSSZ  (PAGESZ/WORDSZ*1)    /*words --- return stack size*/
#define AUXSSZ  (64)    /*words --- auxiliary data stack size*/ 

#define CM_N 7
typedef enum {
   CM_NOOP   = 0x00, /* no op */
   CM_RETURN = 0x01, /* return */
   CM_PUSHV  = 0x02, /* push value */
   CM_PUSHA  = 0x03, /* push pc+2, and jump offs */
   CM_PCALL  = 0x04, /* primitive call --- not produced by compiler*/
   CM_SCALL  = 0x05, /* stack call --- apply */
   CM_CALL   = 0x06  /* call */
} Command;

static char *scommand[] = {
   "noop  ","return","pushv ","pusha ","pcall ","scall ","call  "
};


typedef enum {
   TK_EOI    = 0x00, /* end of input */
   TK_SYMBOL = 0x01, /* symbol; max SYMBSZ-1 char long */
   TK_QSYMBOL= 0x02, /* 'symbol; max SYMBSZ-1 char long */
   TK_SOPEN  = 0x03, /* [ open square bracket */
   TK_SCLOSE = 0x04, /* ] close square bracket */
   TK_INTEGER= 0x05, /* 31 bit non-negative integer */
   TK_APPLY  = 0x06, /* @ apply */
   TK_STRING = 0x07, /* string */
   TK_WHITE  = 0x08, /* white space -- ignored by compiler */
   TK_COMMENT= 0x09  /* comment --- ignored by compiler*/
} Token;

typedef enum {
   ER_OK = 0,
   ER_FATAL = 1,
   ER_LOOKUP = 2,
   ER_NOTIMPL = 3
} ErrorCode;

static char *serrors[] = {
   "COOL","UNKERR","SYMLUP", "NOTIMP"
};


typedef int Input(void);

/* Dictionary entry offsets in words*/
#define DE_NEXT 0
#define DE_CODE 1
#define DE_NAME 2
#define DE_SIZE (SYMWSZ+2)


typedef struct {
   long dc[DICTSZ]; /*dictionary*/
   long hd; /* head dict entry offset */
   long dp; /* offs of first free word in dict */
   long pc; /*program counter; dictionary offset*/

   long rs[RETSSZ]; /*return stack*/
   long rp;         /*return stack pointer*/
   long ds[DATSSZ]; /*data stack*/
   long sp;         /*data stack pointer*/
   long as[AUXSSZ]; /* auxiliary data stack */
   long ap;         /* auxiliary data stack pointer */

   Input *input;
   char sbuf[STRBSZ]; /*lexer temp string buffer; \0 terminated symbols and strings*/
   long ibuf; /*lexer temp int buffer */
   int uninput; /* lexer 1 char "unget" buffer */

   ErrorCode err;
   int debug;
   long count;
   long pcount;
} Engine;

typedef void Primitive(Engine *e);

void define(Engine *e, long code, char *s) {
   char *p;
   e->dc[e->dp+DE_NEXT]=e->hd;
   e->hd=e->dp;
   e->dc[e->dp+DE_CODE]=code;

   p=(char*)&(e->dc[e->dp+DE_NAME]);
   strncpy(p,s,SYMBSZ-1);
   p[SYMBSZ-1]=0;
   e->dp += DE_SIZE;
}

void definePrimitive(Engine *e,Primitive *f,char *s) {
   long code;
   code=e->dp;
   e->dc[e->dp++]=CM_PCALL;
   e->dc[e->dp++]=(long)f;
   e->dc[e->dp++]=CM_RETURN;
   define(e,code,s);
}

long lookup(Engine *e, char *s) {
   long p;
   for (p=e->hd;p;p=e->dc[p+DE_NEXT]) {
      if (strcmp(s,(char*)&(e->dc[p+DE_NAME]))==0) {
         return p;
      }
   }
   return 0;
}


void f_if(Engine *e) { /* (cf ct bc -- ((bc?ct:cf)@)) */
   long cf,ct,bc;
   bc = e->ds[--e->sp];
   ct = e->ds[--e->sp];
   cf = e->ds[--e->sp];
   if (e->dc[e->rs[e->rp-1]]!=CM_RETURN) {
      e->rs[e->rp++]=e->pc;
   }
   e->pc=(bc?ct:cf);
}

void f_cond(Engine *e) { /* (cf ct bc -- (bc?ct:cf)) */
   long cf,ct,bc;
   bc = e->ds[--e->sp];
   ct = e->ds[--e->sp];
   cf = e->ds[--e->sp];
   e->ds[e->sp++]=(bc?ct:cf);
}

void f_deci(Engine *e) { /* (ix -- (ix-1)) */
   e->ds[e->sp-1]--;
}

void f_inci(Engine *e) { /* (ix -- (ix-1)) */
   e->ds[e->sp-1]++;
}

void f_addi(Engine *e) { /* (iy ix -- (ix+iy)) */
   long a,b;
   a = e->ds[--e->sp];
   b = e->ds[--e->sp];
   e->ds[e->sp++]=a+b;
}
void f_subi(Engine *e) { /* (iy ix -- (ix-iy)) */
   long a,b;
   a = e->ds[--e->sp];
   b = e->ds[--e->sp];
   e->ds[e->sp++]=a-b;
}
void f_muli(Engine *e) { /* (iy ix -- (ix*iy)) */
   long a,b;
   a = e->ds[--e->sp];
   b = e->ds[--e->sp];
   e->ds[e->sp++]=a*b;
}
void f_divi(Engine *e) { /* (iy ix -- (ix/iy)) */
   long a,b;
   a = e->ds[--e->sp];
   b = e->ds[--e->sp];
   e->ds[e->sp++]=a/b;
}
void f_umii(Engine *e) { /* (ix -- (-ix)) */
   e->ds[e->sp-1]= -(e->ds[e->sp-1]);
}

void f_eqi(Engine *e) { /* (iy ix -- (ix=iy)) */
   long a,b;
   a = e->ds[--e->sp];
   b = e->ds[--e->sp];
   e->ds[e->sp++]=(a==b);
}
void f_gti(Engine *e) { /* (iy ix -- (ix>iy)) */
   long a,b;
   a = e->ds[--e->sp];
   b = e->ds[--e->sp];
   e->ds[e->sp++]=(a>b);
}
void f_andi(Engine *e) { /* (iy ix -- (ix&iy)) */
   long a,b;
   a = e->ds[--e->sp];
   b = e->ds[--e->sp];
   e->ds[e->sp++]=(a&b);
}
void f_ori(Engine *e) { /* (iy ix -- (ix|iy)) */
   long a,b;
   a = e->ds[--e->sp];
   b = e->ds[--e->sp];
   e->ds[e->sp++]=(a|b);
}
void f_negi(Engine *e) { /* (ix -- (~ix)) */
   e->ds[e->sp-1]= ~(e->ds[e->sp-1]);
}

void f_apush(Engine *e) { /* (x -- ) */
   e->as[e->ap++]=e->ds[--e->sp];
}
void f_apop(Engine *e) { /* ( -- x) */
   e->ds[e->sp++]=e->as[--e->ap];
}

void f_dup(Engine *e) { /* (x -- x x) */
   e->ds[e->sp++]=e->ds[e->sp-1];
}

void f_dup2(Engine *e) { /* (y x -- y x y x) */
   e->ds[e->sp++]=e->ds[e->sp-2];
   e->ds[e->sp++]=e->ds[e->sp-2];
}

void f_drop(Engine *e) { /* ( x -- ) */
   e->sp--;
}

void f_drop2(Engine *e) { /* (y x -- ) */
   e->sp-=2;
}

void f_swap(Engine *e) { /* (y x -- x y) */
   e->ds[e->sp]=e->ds[e->sp-1];
   e->ds[e->sp-1]=e->ds[e->sp-2];
   e->ds[e->sp-2]=e->ds[e->sp];
}

void f_swap2(Engine *e) { /* (y1 y2 x1 x2 -- x1 x2 y1 y2) */
   e->ds[e->sp]=e->ds[e->sp-1];
   e->ds[e->sp-1]=e->ds[e->sp-3];
   e->ds[e->sp-3]=e->ds[e->sp];
   e->ds[e->sp]=e->ds[e->sp-2];
   e->ds[e->sp-2]=e->ds[e->sp-4];
   e->ds[e->sp-4]=e->ds[e->sp];
}

void f_rot(Engine *e) { /* (z y x -- y x z) */
   e->ds[e->sp]=e->ds[e->sp-3];
   e->ds[e->sp-3]=e->ds[e->sp-2];
   e->ds[e->sp-2]=e->ds[e->sp-1];
   e->ds[e->sp-1]=e->ds[e->sp];
}

void f_rotneg(Engine *e) { /* (z y x -- x z y) */
   e->ds[e->sp]=e->ds[e->sp-3];
   e->ds[e->sp-3]=e->ds[e->sp-1];
   e->ds[e->sp-1]=e->ds[e->sp-2];
   e->ds[e->sp-2]=e->ds[e->sp];
}



void f_over(Engine *e) { /* (y x -- y x y) */
   e->ds[e->sp++]=e->ds[e->sp-2];
}

void f_over2(Engine *e) { /* (y1 y2 x1 x2 -- y1 y2 x1 x2 y1 y2) */
   e->ds[e->sp++]=e->ds[e->sp-4];
   e->ds[e->sp++]=e->ds[e->sp-4];
}

void f_pick(Engine *e) { /* ( ix -- (ix-th element)) */
   long ix;
   ix = e->ds[--e->sp];
   e->ds[e->sp++]=e->ds[e->sp-ix-1];
}

void f_printi(Engine *e) { /* ( ix -- ) */
   printf("%ld",e->ds[--e->sp]);
   fflush(stdout);
}

void f_prints(Engine *e) { /* ( sx -- ) */
   printf("%s",(char*)&(e->dc[e->ds[--e->sp]]));
   fflush(stdout);
}


void f_define(Engine *e) { /* ( code name -- ) */
   long code;
   char *name;

   name=(char*)&(e->dc[e->ds[--e->sp]]);
   code=e->ds[--e->sp];

   define(e,code,name);
}

void f_redefine(Engine *e) { /* ( code name -- ) */
   long code;
   char *name;
   long de;

   name=(char*)&(e->dc[e->ds[--e->sp]]);
   code=e->ds[--e->sp];
   de = lookup(e,name);
   if (de==0) {
      define(e,code,name);
   } else {
      e->dc[de+DE_CODE]=code;
   }
}

void f_lookup(Engine *e) { /* ( name -- code ) */
   char *name;
   long de;

   name=(char*)&(e->dc[e->ds[--e->sp]]);
   de = lookup(e,name);
   if (de==0) {
      e->ds[e->sp++]=0;
   } else {
      e->ds[e->sp++]=e->dc[de+DE_CODE];
   }
}



void reset(Engine *e,int _debug, Input *inp) {
   /*we use 0 for NULL pointer; place an empty dict entry at 0*/
   for (e->dp=0; e->dp!=10; e->dp++) {
      e->dc[e->dp]=0;
   }
   e->hd=0; /*points to empty entry*/
   e->rp=0;
   e->sp=0;
   e->ap=0;
   e->input=inp;
   e->err=ER_OK;
   e->debug=_debug;
   e->ibuf=0;
   e->sbuf[0]=0;
   e->uninput=0;
   e->count=0;
   e->pcount=0;

   definePrimitive(e,f_define,"def");
   definePrimitive(e,f_redefine,"redefine");
   definePrimitive(e,f_lookup,"lookup");

   definePrimitive(e,f_inci,"inc");
   definePrimitive(e,f_deci,"dec");
   definePrimitive(e,f_addi,"+");
   definePrimitive(e,f_subi,"-");
   definePrimitive(e,f_muli,"*");
   definePrimitive(e,f_divi,"/");
   definePrimitive(e,f_umii,"neg");
   definePrimitive(e,f_eqi,"=");
   definePrimitive(e,f_gti,">");
   definePrimitive(e,f_andi,"&");
   definePrimitive(e,f_ori,"|");
   definePrimitive(e,f_negi,"~");

   definePrimitive(e,f_dup,"dup");
   definePrimitive(e,f_dup2,"dup2");
   definePrimitive(e,f_drop,"drop");
   definePrimitive(e,f_drop2,"drop2");
   definePrimitive(e,f_swap,"swap");
   definePrimitive(e,f_swap2,"swap2");
   definePrimitive(e,f_rot,"rot");
   definePrimitive(e,f_rotneg,"-rot");
   definePrimitive(e,f_over,"over");
   definePrimitive(e,f_over2,"over2");
   definePrimitive(e,f_pick,"pick");
   definePrimitive(e,f_apush,">a");
   definePrimitive(e,f_apop,"a>");

   definePrimitive(e,f_printi,".");
   definePrimitive(e,f_prints,"s.");

   definePrimitive(e,f_cond,"cond");
   definePrimitive(e,f_if,"if");
}

Token lexer(Engine *e) {
   int c,i,qflag,eflag;
   qflag=0;
   if (e->uninput!=0) {
      c = e->uninput;
      e->uninput=0;
   } else {
      c = e->input();
   }
   for (;c==' '||c=='\t'||c=='\n'||c=='\r'; c=e->input()) ;
   switch (c) {
      case EOF:
         return TK_EOI;
      case '[':
         return TK_SOPEN;
      case ']':
         return TK_SCLOSE;
      case '@':
         return TK_APPLY;
      case '"':
         c=e->input();
         eflag=0;
         for (i=0;i!=STRBSZ-1&&(c!='"'||eflag)&&c!=EOF;c=e->input()) {
            if (c=='\r') { /* dos \r filtered out */
               continue;
            }
            if (!eflag&&c=='\\') {
               eflag=1;
            } else {
               if (eflag) {
                  if (c=='\n') { /* eol \ supresses \n */
                     continue;
                  }
                  eflag=0;
                  switch (c) {
                     case 't': c='\t'; break;
                     case 'r': c='\r'; break;
                     case 'n': c='\n'; break;
                     case 'f': c='\f'; break;
                     default: break;
                  }
               }
               e->sbuf[i++]=c;
            }
         }
         e->sbuf[i]=0;
         e->ibuf=i;
         if (c!='"') {
            e->uninput=c;
         }
         return TK_STRING;
   }
   if (c>='0'&&c<='9') {
      e->ibuf=c-'0';
      while ((c=e->input())>='0'&&c<='9') {
         e->ibuf=e->ibuf*10+c-'0';
      }
      e->uninput=c;
      return TK_INTEGER;
   }

   for (i=0; i!=SYMBSZ-1&&c!=EOF&&c!=' '&&c!='\t'&&c!='\n'&&c!='\r'&&c!='['&&c!=']'&&c!='"'; i++,(c=e->input()) ) {
      if (i==0&&c=='\'') {
         qflag=1;
         i--;
      } else {
         e->sbuf[i]=c;
      }
   }
   e->sbuf[i]=0;
   if (!qflag&&e->sbuf[0]=='-'&&e->sbuf[1]=='-') { /*comment*/
      for (;c!=EOF&&c!='\n';c=e->input()) ;
      e->uninput=c;
      return TK_COMMENT;
   } else {
      e->uninput=c;
      return (qflag)?TK_QSYMBOL:TK_SYMBOL;
   }
}

void compile(Engine *e) { //uses data stack to handle square brackets
   Token t;
   long de,wsz;
   if (e->debug) printf("c>\n");
   e->pc=e->dp;
   while ((t=lexer(e))!=TK_EOI) {
      switch (t) {
         case TK_INTEGER:
            if (e->debug) printf("c> %ld: pushv %ld\n",e->dp,e->ibuf);
            e->dc[e->dp++]=CM_PUSHV;
            e->dc[e->dp++]=e->ibuf;
            break;
         case TK_QSYMBOL:
            de=lookup(e,e->sbuf);
            if (de==0) {
               e->err=ER_LOOKUP;
               return;
            }
            if (e->debug) {
               printf("c> %ld: pushv %ld(%s)\n",e->dp,e->dc[de+DE_CODE],e->sbuf);
            }
            e->dc[e->dp++]=CM_PUSHV;
            e->dc[e->dp++]=e->dc[de+DE_CODE];

            break;
         case TK_SYMBOL:
            de=lookup(e,e->sbuf);
            if (de==0) {
               e->err=ER_LOOKUP;
               return;
            }
            if (e->debug) {
               printf("c> %ld: call %ld(%s)\n",e->dp,e->dc[de+DE_CODE],e->sbuf);
            }
            e->dc[e->dp++]=CM_CALL;
            e->dc[e->dp++]=e->dc[de+DE_CODE];
            break;
         case TK_APPLY:
            if (e->debug) printf("c> %ld: scall\n",e->dp);
            e->dc[e->dp++]=CM_SCALL;
            break;
         case TK_STRING:
            if (e->debug) printf("c> %ld: pusha (string) %ld bytes\n",e->dp,e->ibuf);
            e->dc[e->dp++]=CM_PUSHA;
            wsz=(e->ibuf+1+WORDSZ-1)/WORDSZ;
            e->dc[e->dp++]=e->dp+wsz+1;
            strcpy((char*)&(e->dc[e->dp]),e->sbuf);
            e->dp += wsz;
            break;
         case TK_SOPEN:
            if (e->debug) printf("c> %ld: pusha\n",e->dp);
            e->dc[e->dp++]=CM_PUSHA;
            e->ds[e->sp++]=e->dp++;
            break;
         case TK_SCLOSE:
            if (e->debug) printf("c> %ld: return\n",e->dp);
            if (e->debug) printf("c> __%ld__\n",e->ds[e->sp-1]-1);
            e->dc[e->dp++]=CM_RETURN;
            e->dc[e->ds[--e->sp]]=e->dp;
            break;
         case TK_WHITE:
         case TK_COMMENT:
            break;
      }
   }
   if (e->debug) printf("c> %ld: return\n",e->dp);
   e->dc[e->dp++]=CM_RETURN;
   if (e->debug) printf("c>\n");
   return;
}

void execute(Engine *e) {
   long cmd,p;
   Primitive *f;
   while (1) {
      e->count++;
      cmd=e->dc[e->pc++];
      switch (cmd) {
         case CM_NOOP: /* do nothing! */
            break;
         case CM_PUSHV:
            e->ds[e->sp++]=e->dc[e->pc++];
            break;
         case CM_PUSHA:
            e->ds[e->sp++]=e->pc+1;
            e->pc=e->dc[e->pc];
            break;
         case CM_PCALL:
            e->pcount++;
            f = (Primitive*)(e->dc[e->pc++]);
            f(e);
            if (e->err!=ER_OK) {
                return;
            }
            break;
         case CM_CALL:
            if (e->dc[e->pc+1]!=CM_RETURN) { //tro
               e->rs[e->rp++]=e->pc+1;
            }
            e->pc=e->dc[e->pc];
            break;
         case CM_SCALL:
            if (e->dc[e->pc]!=CM_RETURN) { //tro
               e->rs[e->rp++]=e->pc;
            }
            e->pc=e->ds[--e->sp];
            break;
         case CM_RETURN:
            if (e->rp==0) {
               return;
            }
            e->pc=e->rs[--e->rp];
            break;
         default:
            e->err=ER_NOTIMPL;
            return;
      }
      if (e->debug) {
         printf("e> %s ",scommand[cmd]);
         for (p=0;p!=e->sp;p++) {
            printf("%ld ",e->ds[p]);
         }
         printf("; ");
         for (p=0;p!=e->ap;p++) {
            printf("%ld ",e->as[p]);
         }
         printf("; ");
         for (p=0;p!=e->rp;p++) {
            printf("%ld ",e->rs[p]);
         }
         printf("\n");
      }

   }
}

void printDataStack(Engine *e) {
   long p;
   printf("DS(%ld words): ",e->sp);
   for (p=0; p!=e->sp; p++) {
      printf("%ld ",e->ds[p]);
   }
   printf("\n");
}

void printAuxDataStack(Engine *e) {
   long p;
   printf("AS(%ld words): ",e->ap);
   for (p=0; p!=e->ap; p++) {
      printf("%ld ",e->as[p]);
   }
   printf("\n");
}

void printReturnStack(Engine *e) {
   long p;
   printf("RS(%ld words): ",e->rp);
   for (p=0; p!=e->rp; p++) {
      printf("%ld ",e->rs[p]);
   }
   printf("\n");
}

void printRegisters(Engine *e) {
   printf("Registers: ");
   printf("hd=%ld, ",e->hd);
   printf("dp=%ld, ",e->dp);
   printf("pc=%ld, ",e->pc);
   printf("rp=%ld, ",e->rp);
   printf("sp=%ld, ",e->sp);
   printf("ap=%ld, ",e->ap);
   printf("er=%ld(%s), ",e->err,serrors[e->err]);
   printf("ib=%ld, ",e->ibuf);
   printf("sb='%s', ",e->sbuf);
   printf("co=%ld, ",e->count);
   printf("po=%ld\n",e->pcount);
}

void printDictionary(Engine *e) {
   long p;
   long cmd;
   printf("\n\nDictionary entries:\n");
   for (p=e->hd;p;p=e->dc[p+DE_NEXT]) {
      printf("%ld: %ld, %ld, '%s'\n", p,e->dc[p+DE_NEXT],
         e->dc[p+DE_CODE],(char*)&(e->dc[p+DE_NAME])
      );
   }
   printf("\n\nDictionary (%ld words):\n",e->dp);
   for (p=0;p!=e->dp;p++) {
      cmd = (e->dc[p]);
      printf("%ld: %ld, 0x%lX, %s\n",p,e->dc[p],e->dc[p],
         (cmd<0||cmd>=CM_N)?"?":scommand[cmd]
      );
   }
}

void printStatus(Engine *e) {
   printf("\nStatus: %d (%s)\n",e->err,serrors[e->err]);
}

void print(Engine *e) {

   long p;
   long cmd;
   printDictionary(e);
   printReturnStack(e);
   printDataStack(e);
   printAuxDataStack(e);
   printRegisters(e);
}

void usage(Engine *e) {
   long p;
   fprintf(stderr,"*** \n");
   fprintf(stderr,"*** IKE a.k.a COOL a.k.a AE a.k.a. ASBF a.k.a. DOG a.k.a. C8L \n");
   fprintf(stderr,"*** Inspired by JOY\n");
   fprintf(stderr,"*** A Stack Based Functional Programming Language\n");
   fprintf(stderr,"*** \n");
   fprintf(stderr,"*** Copyright (c) 2003 Igor Khomyakov\n");
   fprintf(stderr,"*** $Id: ike.c,v 1.26 2006/05/26 05:48:54 ikh Exp $\n");
   fprintf(stderr,"***\n");
   fprintf(stderr,"usage: ike[d] { file | - | =code } ...\n");
   fprintf(stderr,"tokens: [ ] @ name \"string\" integer --comment\n");
   fprintf(stderr,"dictionary: ");
   for (p=e->hd;p;p=e->dc[p+DE_NEXT]) {
      fprintf(stderr,"%s ",(char*)&(e->dc[p+DE_NAME]));
   }
   fprintf(stderr,"\n\n");
}


static char *program;
int getcharstr(void) {
  if (*program) {
     return *program++;
  } else {
     return EOF;
  }
}

static FILE *finp;
int getcharfile(void) {
  return getc(finp);
}

Engine eng;

int main (int argc, char *argv[]) {
   int debug;
   char *finpnm;
   int i;

   Engine *peng;
   Input *inp=getchar;

   if (argv[0][strlen(argv[0])-1]=='d') {
      debug=1;
   } else {
      debug=0;
   }

   peng=&eng;
   reset(peng,debug,getcharfile);


   if (argc<2) {
      usage(peng);
      return -1;
   }

   for (i=1;i<argc;i++) {
      finpnm=argv[i];
      //printf("Processing '%s' ... \n",finpnm);
      fflush(stdout);
      if (strcmp(finpnm,"-")==0) {
         finp=stdin;
         peng->input=getcharfile;
      } else if (finpnm[0]=='=') {
         finp=stdin;
         peng->input=getcharstr;
         program=&finpnm[1];
      } else {
         finp=fopen(finpnm,"r");
         peng->input=getcharfile;
      }
      if (finp!=NULL) {
         compile(peng);
         fclose(finp);
         if (peng->err==ER_OK) {
            execute(peng);
         }
         if (peng->err!=ER_OK) {
            printf("\nFAILED. I stop.\n");
            printDataStack(peng);
            printAuxDataStack(peng);
            printReturnStack(peng);
            printRegisters(peng);
            return peng->err;
         } else {
            //printf("\n\nOK (count=%ld, pcount=%ld)\n",peng->count,peng->pcount);
            peng->count=0;
            peng->pcount=0;
            //printDataStack(peng);
            //printAuxDataStack(peng);
            //printReturnStack(peng);
            //printRegisters(peng);
            //printDictionary(peng);
         }
      
      } else {
         printf("SKIPPED. Could not open '%s'. I proceed.\n",finpnm);
      }
   }
   return peng->err;
}
