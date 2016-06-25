/* A Bison parser, made by GNU Bison 1.875.  */

/* Skeleton parser for Yacc-like parsing with Bison,
   Copyright (C) 1984, 1989, 1990, 2000, 2001, 2002 Free Software Foundation, Inc.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2, or (at your option)
   any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place - Suite 330,
   Boston, MA 02111-1307, USA.  */

/* As a special exception, when this file is copied by Bison into a
   Bison output file, you may use that output file without restriction.
   This special exception was added by the Free Software Foundation
   in version 1.24 of Bison.  */

/* Tokens.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
   /* Put the tokens into the symbol table, so that GDB and other debuggers
      know about them.  */
   enum Int_yytokentype {
     CONST_P = 258,
     ID = 259,
     OPEN = 260,
     XCLOSE = 261,
     XCREATE = 262,
     INSERT_TUPLE = 263,
     XDECLARE = 264,
     INDEX = 265,
     ON = 266,
     USING = 267,
     XBUILD = 268,
     INDICES = 269,
     UNIQUE = 270,
     COMMA = 271,
     EQUALS = 272,
     LPAREN = 273,
     RPAREN = 274,
     OBJ_ID = 275,
     XBOOTSTRAP = 276,
     XSHARED_RELATION = 277,
     XWITHOUT_OIDS = 278,
     NULLVAL = 279,
     low = 280,
     high = 281
   };
#endif
#define CONST_P 258
#define ID 259
#define OPEN 260
#define XCLOSE 261
#define XCREATE 262
#define INSERT_TUPLE 263
#define XDECLARE 264
#define INDEX 265
#define ON 266
#define USING 267
#define XBUILD 268
#define INDICES 269
#define UNIQUE 270
#define COMMA 271
#define EQUALS 272
#define LPAREN 273
#define RPAREN 274
#define OBJ_ID 275
#define XBOOTSTRAP 276
#define XSHARED_RELATION 277
#define XWITHOUT_OIDS 278
#define NULLVAL 279
#define low 280
#define high 281




#if ! defined (YYSTYPE) && ! defined (YYSTYPE_IS_DECLARED)
#line 83 "bootparse.y"
typedef union YYSTYPE {
	List		*list;
	IndexElem	*ielem;
	char		*str;
	int			ival;
	Oid			oidval;
} YYSTYPE;
/* Line 1248 of yacc.c.  */
#line 96 "y.tab.h"
# define Int_yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
# define YYSTYPE_IS_TRIVIAL 1
#endif

extern YYSTYPE Int_yylval;



