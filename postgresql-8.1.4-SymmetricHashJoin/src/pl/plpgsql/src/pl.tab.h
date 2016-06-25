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
#ifndef PLPGSQL_YYTOKENTYPE
# define PLPGSQL_YYTOKENTYPE
   /* Put the tokens into the symbol table, so that GDB and other debuggers
      know about them.  */
   enum plpgsql_yytokentype {
     K_ALIAS = 258,
     K_ASSIGN = 259,
     K_BEGIN = 260,
     K_CLOSE = 261,
     K_CONSTANT = 262,
     K_CONTINUE = 263,
     K_CURSOR = 264,
     K_DEBUG = 265,
     K_DECLARE = 266,
     K_DEFAULT = 267,
     K_DIAGNOSTICS = 268,
     K_DOTDOT = 269,
     K_ELSE = 270,
     K_ELSIF = 271,
     K_END = 272,
     K_EXCEPTION = 273,
     K_EXECUTE = 274,
     K_EXIT = 275,
     K_FOR = 276,
     K_FETCH = 277,
     K_FROM = 278,
     K_GET = 279,
     K_IF = 280,
     K_IN = 281,
     K_INFO = 282,
     K_INTO = 283,
     K_IS = 284,
     K_LOG = 285,
     K_LOOP = 286,
     K_NEXT = 287,
     K_NOT = 288,
     K_NOTICE = 289,
     K_NULL = 290,
     K_OPEN = 291,
     K_OR = 292,
     K_PERFORM = 293,
     K_ROW_COUNT = 294,
     K_RAISE = 295,
     K_RENAME = 296,
     K_RESULT_OID = 297,
     K_RETURN = 298,
     K_RETURN_NEXT = 299,
     K_REVERSE = 300,
     K_SELECT = 301,
     K_THEN = 302,
     K_TO = 303,
     K_TYPE = 304,
     K_WARNING = 305,
     K_WHEN = 306,
     K_WHILE = 307,
     T_FUNCTION = 308,
     T_TRIGGER = 309,
     T_STRING = 310,
     T_NUMBER = 311,
     T_SCALAR = 312,
     T_ROW = 313,
     T_RECORD = 314,
     T_DTYPE = 315,
     T_LABEL = 316,
     T_WORD = 317,
     T_ERROR = 318,
     O_OPTION = 319,
     O_DUMP = 320
   };
#endif
#define K_ALIAS 258
#define K_ASSIGN 259
#define K_BEGIN 260
#define K_CLOSE 261
#define K_CONSTANT 262
#define K_CONTINUE 263
#define K_CURSOR 264
#define K_DEBUG 265
#define K_DECLARE 266
#define K_DEFAULT 267
#define K_DIAGNOSTICS 268
#define K_DOTDOT 269
#define K_ELSE 270
#define K_ELSIF 271
#define K_END 272
#define K_EXCEPTION 273
#define K_EXECUTE 274
#define K_EXIT 275
#define K_FOR 276
#define K_FETCH 277
#define K_FROM 278
#define K_GET 279
#define K_IF 280
#define K_IN 281
#define K_INFO 282
#define K_INTO 283
#define K_IS 284
#define K_LOG 285
#define K_LOOP 286
#define K_NEXT 287
#define K_NOT 288
#define K_NOTICE 289
#define K_NULL 290
#define K_OPEN 291
#define K_OR 292
#define K_PERFORM 293
#define K_ROW_COUNT 294
#define K_RAISE 295
#define K_RENAME 296
#define K_RESULT_OID 297
#define K_RETURN 298
#define K_RETURN_NEXT 299
#define K_REVERSE 300
#define K_SELECT 301
#define K_THEN 302
#define K_TO 303
#define K_TYPE 304
#define K_WARNING 305
#define K_WHEN 306
#define K_WHILE 307
#define T_FUNCTION 308
#define T_TRIGGER 309
#define T_STRING 310
#define T_NUMBER 311
#define T_SCALAR 312
#define T_ROW 313
#define T_RECORD 314
#define T_DTYPE 315
#define T_LABEL 316
#define T_WORD 317
#define T_ERROR 318
#define O_OPTION 319
#define O_DUMP 320




#if ! defined (PLPGSQL_YYSTYPE) && ! defined (PLPGSQL_YYSTYPE_IS_DECLARED)
#line 64 "gram.y"
typedef union PLPGSQL_YYSTYPE {
		int32					ival;
		bool					boolean;
		char					*str;
		struct
		{
			char *name;
			int  lineno;
		}						varname;
		struct
		{
			char *name;
			int  lineno;
			PLpgSQL_rec     *rec;
			PLpgSQL_row     *row;
		}						forvariable;
		struct
		{
			char *label;
			int  n_initvars;
			int  *initvarnos;
		}						declhdr;
		struct
		{
			char *end_label;
			List *stmts;
		}						loop_body;
		List					*list;
		PLpgSQL_type			*dtype;
		PLpgSQL_datum			*scalar;	/* a VAR, RECFIELD, or TRIGARG */
		PLpgSQL_variable		*variable;	/* a VAR, REC, or ROW */
		PLpgSQL_var				*var;
		PLpgSQL_row				*row;
		PLpgSQL_rec				*rec;
		PLpgSQL_expr			*expr;
		PLpgSQL_stmt			*stmt;
		PLpgSQL_stmt_block		*program;
		PLpgSQL_condition		*condition;
		PLpgSQL_exception		*exception;
		PLpgSQL_exception_block	*exception_block;
		PLpgSQL_nsitem			*nsitem;
		PLpgSQL_diag_item		*diagitem;
} PLPGSQL_YYSTYPE;
/* Line 1248 of yacc.c.  */
#line 210 "y.tab.h"
# define plpgsql_yystype PLPGSQL_YYSTYPE /* obsolescent; will be withdrawn */
# define PLPGSQL_YYSTYPE_IS_DECLARED 1
# define PLPGSQL_YYSTYPE_IS_TRIVIAL 1
#endif

extern PLPGSQL_YYSTYPE plpgsql_yylval;



