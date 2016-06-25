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

/* Written by Richard Stallman by simplifying the original so called
   ``semantic'' parser.  */

/* All symbols defined below should begin with plpgsql_yy or PLPGSQL_YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output.  */
#define PLPGSQL_YYBISON 1

/* Skeleton name.  */
#define PLPGSQL_YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define PLPGSQL_YYPURE 0

/* Using locations.  */
#define PLPGSQL_YYLSP_NEEDED 0



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




/* Copy the first part of user declarations.  */
#line 1 "gram.y"

/**********************************************************************
 * gram.y				- Parser for the PL/pgSQL
 *						  procedural language
 *
 * IDENTIFICATION
 *	  $PostgreSQL: pgsql/src/pl/plpgsql/src/gram.y,v 1.82.2.1 2006/03/23 04:22:44 tgl Exp $
 *
 *	  This software is copyrighted by Jan Wieck - Hamburg.
 *
 *	  The author hereby grants permission  to  use,  copy,	modify,
 *	  distribute,  and	license this software and its documentation
 *	  for any purpose, provided that existing copyright notices are
 *	  retained	in	all  copies  and  that	this notice is included
 *	  verbatim in any distributions. No written agreement, license,
 *	  or  royalty  fee	is required for any of the authorized uses.
 *	  Modifications to this software may be  copyrighted  by  their
 *	  author  and  need  not  follow  the licensing terms described
 *	  here, provided that the new terms are  clearly  indicated  on
 *	  the first page of each file where they apply.
 *
 *	  IN NO EVENT SHALL THE AUTHOR OR DISTRIBUTORS BE LIABLE TO ANY
 *	  PARTY  FOR  DIRECT,	INDIRECT,	SPECIAL,   INCIDENTAL,	 OR
 *	  CONSEQUENTIAL   DAMAGES  ARISING	OUT  OF  THE  USE  OF  THIS
 *	  SOFTWARE, ITS DOCUMENTATION, OR ANY DERIVATIVES THEREOF, EVEN
 *	  IF  THE  AUTHOR  HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH
 *	  DAMAGE.
 *
 *	  THE  AUTHOR  AND	DISTRIBUTORS  SPECIFICALLY	 DISCLAIM	ANY
 *	  WARRANTIES,  INCLUDING,  BUT	NOT  LIMITED  TO,  THE	IMPLIED
 *	  WARRANTIES  OF  MERCHANTABILITY,	FITNESS  FOR  A  PARTICULAR
 *	  PURPOSE,	AND NON-INFRINGEMENT.  THIS SOFTWARE IS PROVIDED ON
 *	  AN "AS IS" BASIS, AND THE AUTHOR	AND  DISTRIBUTORS  HAVE  NO
 *	  OBLIGATION   TO	PROVIDE   MAINTENANCE,	 SUPPORT,  UPDATES,
 *	  ENHANCEMENTS, OR MODIFICATIONS.
 *
 **********************************************************************/

#include "plpgsql.h"

#include "parser/parser.h"

static PLpgSQL_expr		*read_sql_construct(int until,
											int until2,
											const char *expected,
											const char *sqlstart,
											bool isexpression,
											bool valid_sql,
											int *endtoken);
static	PLpgSQL_expr	*read_sql_stmt(const char *sqlstart);
static	PLpgSQL_type	*read_datatype(int tok);
static	PLpgSQL_stmt	*make_select_stmt(void);
static	PLpgSQL_stmt	*make_fetch_stmt(void);
static	void			 check_assignable(PLpgSQL_datum *datum);
static	PLpgSQL_row		*read_into_scalar_list(const char *initial_name,
											   PLpgSQL_datum *initial_datum);
static	void			 check_sql_expr(const char *stmt);
static	void			 plpgsql_sql_error_callback(void *arg);
static	void			 check_labels(const char *start_label,
									  const char *end_label);



/* Enabling traces.  */
#ifndef PLPGSQL_YYDEBUG
# define PLPGSQL_YYDEBUG 0
#endif

/* Enabling verbose error messages.  */
#ifdef PLPGSQL_YYERROR_VERBOSE
# undef PLPGSQL_YYERROR_VERBOSE
# define PLPGSQL_YYERROR_VERBOSE 1
#else
# define PLPGSQL_YYERROR_VERBOSE 0
#endif

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
/* Line 191 of yacc.c.  */
#line 312 "y.tab.c"
# define plpgsql_yystype PLPGSQL_YYSTYPE /* obsolescent; will be withdrawn */
# define PLPGSQL_YYSTYPE_IS_DECLARED 1
# define PLPGSQL_YYSTYPE_IS_TRIVIAL 1
#endif



/* Copy the second part of user declarations.  */


/* Line 214 of yacc.c.  */
#line 324 "y.tab.c"

#if ! defined (plpgsql_yyoverflow) || PLPGSQL_YYERROR_VERBOSE

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# if PLPGSQL_YYSTACK_USE_ALLOCA
#  define PLPGSQL_YYSTACK_ALLOC alloca
# else
#  ifndef PLPGSQL_YYSTACK_USE_ALLOCA
#   if defined (alloca) || defined (_ALLOCA_H)
#    define PLPGSQL_YYSTACK_ALLOC alloca
#   else
#    ifdef __GNUC__
#     define PLPGSQL_YYSTACK_ALLOC __builtin_alloca
#    endif
#   endif
#  endif
# endif

# ifdef PLPGSQL_YYSTACK_ALLOC
   /* Pacify GCC's `empty if-body' warning. */
#  define PLPGSQL_YYSTACK_FREE(Ptr) do { /* empty */; } while (0)
# else
#  if defined (__STDC__) || defined (__cplusplus)
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   define PLPGSQL_YYSIZE_T size_t
#  endif
#  define PLPGSQL_YYSTACK_ALLOC malloc
#  define PLPGSQL_YYSTACK_FREE free
# endif
#endif /* ! defined (plpgsql_yyoverflow) || PLPGSQL_YYERROR_VERBOSE */


#if (! defined (plpgsql_yyoverflow) \
     && (! defined (__cplusplus) \
	 || (PLPGSQL_YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union plpgsql_yyalloc
{
  short plpgsql_yyss;
  PLPGSQL_YYSTYPE plpgsql_yyvs;
  };

/* The size of the maximum gap between one aligned stack and the next.  */
# define PLPGSQL_YYSTACK_GAP_MAXIMUM (sizeof (union plpgsql_yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define PLPGSQL_YYSTACK_BYTES(N) \
     ((N) * (sizeof (short) + sizeof (PLPGSQL_YYSTYPE))				\
      + PLPGSQL_YYSTACK_GAP_MAXIMUM)

/* Copy COUNT objects from FROM to TO.  The source and destination do
   not overlap.  */
# ifndef PLPGSQL_YYCOPY
#  if 1 < __GNUC__
#   define PLPGSQL_YYCOPY(To, From, Count) \
      __builtin_memcpy (To, From, (Count) * sizeof (*(From)))
#  else
#   define PLPGSQL_YYCOPY(To, From, Count)		\
      do					\
	{					\
	  register PLPGSQL_YYSIZE_T plpgsql_yyi;		\
	  for (plpgsql_yyi = 0; plpgsql_yyi < (Count); plpgsql_yyi++)	\
	    (To)[plpgsql_yyi] = (From)[plpgsql_yyi];		\
	}					\
      while (0)
#  endif
# endif

/* Relocate STACK from its old location to the new one.  The
   local variables PLPGSQL_YYSIZE and PLPGSQL_YYSTACKSIZE give the old and new number of
   elements in the stack, and PLPGSQL_YYPTR gives the new location of the
   stack.  Advance PLPGSQL_YYPTR to a properly aligned location for the next
   stack.  */
# define PLPGSQL_YYSTACK_RELOCATE(Stack)					\
    do									\
      {									\
	PLPGSQL_YYSIZE_T plpgsql_yynewbytes;						\
	PLPGSQL_YYCOPY (&plpgsql_yyptr->Stack, Stack, plpgsql_yysize);				\
	Stack = &plpgsql_yyptr->Stack;						\
	plpgsql_yynewbytes = plpgsql_yystacksize * sizeof (*Stack) + PLPGSQL_YYSTACK_GAP_MAXIMUM; \
	plpgsql_yyptr += plpgsql_yynewbytes / sizeof (*plpgsql_yyptr);				\
      }									\
    while (0)

#endif

#if defined (__STDC__) || defined (__cplusplus)
   typedef signed char plpgsql_yysigned_char;
#else
   typedef short plpgsql_yysigned_char;
#endif

/* PLPGSQL_YYFINAL -- State number of the termination state. */
#define PLPGSQL_YYFINAL  9
/* PLPGSQL_YYLAST -- Last index in PLPGSQL_YYTABLE.  */
#define PLPGSQL_YYLAST   400

/* PLPGSQL_YYNTOKENS -- Number of terminals. */
#define PLPGSQL_YYNTOKENS  73
/* PLPGSQL_YYNNTS -- Number of nonterminals. */
#define PLPGSQL_YYNNTS  76
/* PLPGSQL_YYNRULES -- Number of rules. */
#define PLPGSQL_YYNRULES  139
/* PLPGSQL_YYNRULES -- Number of states. */
#define PLPGSQL_YYNSTATES  232

/* PLPGSQL_YYTRANSLATE(PLPGSQL_YYLEX) -- Bison symbol number corresponding to PLPGSQL_YYLEX.  */
#define PLPGSQL_YYUNDEFTOK  2
#define PLPGSQL_YYMAXUTOK   320

#define PLPGSQL_YYTRANSLATE(PLPGSQL_YYX) 						\
  ((unsigned int) (PLPGSQL_YYX) <= PLPGSQL_YYMAXUTOK ? plpgsql_yytranslate[PLPGSQL_YYX] : PLPGSQL_YYUNDEFTOK)

/* PLPGSQL_YYTRANSLATE[PLPGSQL_YYLEX] -- Bison symbol number corresponding to PLPGSQL_YYLEX.  */
static const unsigned char plpgsql_yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
      69,    70,     2,     2,    71,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,    66,
      67,     2,    68,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,    72,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
      55,    56,    57,    58,    59,    60,    61,    62,    63,    64,
      65
};

#if PLPGSQL_YYDEBUG
/* PLPGSQL_YYPRHS[PLPGSQL_YYN] -- Index of the first RHS symbol of rule number PLPGSQL_YYN in
   PLPGSQL_YYRHS.  */
static const unsigned short plpgsql_yyprhs[] =
{
       0,     0,     3,     8,    13,    14,    16,    19,    21,    24,
      25,    27,    35,    37,    40,    44,    46,    49,    51,    57,
      59,    61,    67,    73,    79,    80,    87,    88,    89,    93,
      95,    99,   102,   104,   106,   108,   110,   112,   113,   115,
     116,   117,   120,   122,   124,   126,   128,   129,   131,   134,
     136,   139,   141,   143,   145,   147,   149,   151,   153,   155,
     157,   159,   161,   163,   165,   167,   169,   171,   173,   175,
     179,   184,   190,   194,   196,   200,   202,   204,   206,   208,
     210,   212,   216,   225,   226,   232,   235,   240,   246,   251,
     255,   257,   259,   261,   263,   266,   271,   273,   275,   278,
     281,   286,   288,   290,   292,   294,   296,   298,   300,   306,
     309,   312,   316,   321,   326,   329,   331,   333,   335,   337,
     338,   339,   344,   347,   349,   355,   359,   361,   362,   363,
     364,   365,   366,   372,   373,   375,   377,   379,   382,   384
};

/* PLPGSQL_YYRHS -- A `-1'-separated list of the rules' RHS. */
static const short plpgsql_yyrhs[] =
{
      74,     0,    -1,    53,    75,    79,    78,    -1,    54,    75,
      79,    78,    -1,    -1,    76,    -1,    76,    77,    -1,    77,
      -1,    64,    65,    -1,    -1,    66,    -1,    80,     5,   148,
      99,   135,    17,   145,    -1,   144,    -1,   144,    81,    -1,
     144,    81,    82,    -1,    11,    -1,    82,    83,    -1,    83,
      -1,    67,    67,   147,    68,    68,    -1,    11,    -1,    84,
      -1,    92,    94,    95,    96,    97,    -1,    92,     3,    21,
      91,    66,    -1,    41,    93,    48,    93,    66,    -1,    -1,
      92,     9,    85,    87,    90,    86,    -1,    -1,    -1,    69,
      88,    70,    -1,    89,    -1,    88,    71,    89,    -1,    92,
      95,    -1,    29,    -1,    21,    -1,    62,    -1,    62,    -1,
      62,    -1,    -1,     7,    -1,    -1,    -1,    33,    35,    -1,
      66,    -1,    98,    -1,     4,    -1,    12,    -1,    -1,   100,
      -1,   100,   101,    -1,   101,    -1,    79,    66,    -1,   103,
      -1,   110,    -1,   112,    -1,   113,    -1,   114,    -1,   117,
      -1,   118,    -1,   120,    -1,   121,    -1,   122,    -1,   126,
      -1,   127,    -1,   102,    -1,   104,    -1,   128,    -1,   129,
      -1,   130,    -1,   131,    -1,    38,   148,   140,    -1,   109,
     148,     4,   140,    -1,    24,    13,   148,   105,    66,    -1,
     105,    71,   106,    -1,   106,    -1,   108,     4,   107,    -1,
      39,    -1,    42,    -1,    57,    -1,    57,    -1,    58,    -1,
      59,    -1,   109,    72,   141,    -1,    25,   148,   142,    99,
     111,    17,    25,    66,    -1,    -1,    16,   148,   142,    99,
     111,    -1,    15,    99,    -1,   144,    31,   148,   125,    -1,
     144,    52,   148,   143,   125,    -1,   144,    21,   115,   125,
      -1,   148,   116,    26,    -1,    57,    -1,    62,    -1,    59,
      -1,    58,    -1,    46,   148,    -1,   119,   148,   145,   146,
      -1,    20,    -1,     8,    -1,    43,   148,    -1,    44,   148,
      -1,    40,   148,   124,   123,    -1,    55,    -1,    18,    -1,
      50,    -1,    34,    -1,    27,    -1,    30,    -1,    10,    -1,
      99,    17,    31,   145,    66,    -1,   134,   148,    -1,    19,
     148,    -1,    36,   148,   132,    -1,    22,   148,   133,    28,
      -1,     6,   148,   133,    66,    -1,    35,    66,    -1,    57,
      -1,    57,    -1,    62,    -1,    63,    -1,    -1,    -1,    18,
     148,   136,   137,    -1,   137,   138,    -1,   138,    -1,    51,
     148,   139,    47,    99,    -1,   139,    37,   147,    -1,   147,
      -1,    -1,    -1,    -1,    -1,    -1,    67,    67,   147,    68,
      68,    -1,    -1,    61,    -1,    62,    -1,    66,    -1,    51,
     140,    -1,    62,    -1,    -1
};

/* PLPGSQL_YYRLINE[PLPGSQL_YYN] -- source line where rule number PLPGSQL_YYN was defined.  */
static const unsigned short plpgsql_yyrline[] =
{
       0,   230,   230,   234,   240,   241,   244,   245,   248,   254,
     255,   258,   280,   288,   296,   307,   313,   315,   319,   321,
     323,   327,   361,   366,   371,   370,   417,   429,   432,   461,
     465,   471,   478,   479,   481,   509,   519,   530,   531,   536,
     547,   548,   552,   554,   562,   563,   567,   570,   574,   581,
     590,   592,   594,   596,   598,   600,   602,   604,   606,   608,
     610,   612,   614,   616,   618,   620,   622,   624,   626,   630,
     643,   657,   670,   674,   680,   692,   696,   702,   710,   715,
     720,   725,   740,   756,   759,   788,   794,   811,   829,   868,
    1005,  1015,  1025,  1035,  1047,  1054,  1069,  1073,  1079,  1142,
    1187,  1230,  1236,  1240,  1244,  1248,  1252,  1256,  1262,  1269,
    1282,  1337,  1454,  1466,  1479,  1486,  1503,  1520,  1522,  1527,
    1529,  1528,  1561,  1565,  1571,  1584,  1594,  1601,  1605,  1609,
    1613,  1617,  1621,  1629,  1632,  1638,  1645,  1647,  1651,  1661
};
#endif

#if PLPGSQL_YYDEBUG || PLPGSQL_YYERROR_VERBOSE
/* PLPGSQL_YYTNME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at PLPGSQL_YYNTOKENS, nonterminals. */
static const char *const plpgsql_yytname[] =
{
  "$end", "error", "$undefined", "K_ALIAS", "K_ASSIGN", "K_BEGIN", 
  "K_CLOSE", "K_CONSTANT", "K_CONTINUE", "K_CURSOR", "K_DEBUG", 
  "K_DECLARE", "K_DEFAULT", "K_DIAGNOSTICS", "K_DOTDOT", "K_ELSE", 
  "K_ELSIF", "K_END", "K_EXCEPTION", "K_EXECUTE", "K_EXIT", "K_FOR", 
  "K_FETCH", "K_FROM", "K_GET", "K_IF", "K_IN", "K_INFO", "K_INTO", 
  "K_IS", "K_LOG", "K_LOOP", "K_NEXT", "K_NOT", "K_NOTICE", "K_NULL", 
  "K_OPEN", "K_OR", "K_PERFORM", "K_ROW_COUNT", "K_RAISE", "K_RENAME", 
  "K_RESULT_OID", "K_RETURN", "K_RETURN_NEXT", "K_REVERSE", "K_SELECT", 
  "K_THEN", "K_TO", "K_TYPE", "K_WARNING", "K_WHEN", "K_WHILE", 
  "T_FUNCTION", "T_TRIGGER", "T_STRING", "T_NUMBER", "T_SCALAR", "T_ROW", 
  "T_RECORD", "T_DTYPE", "T_LABEL", "T_WORD", "T_ERROR", "O_OPTION", 
  "O_DUMP", "';'", "'<'", "'>'", "'('", "')'", "','", "'['", "$accept", 
  "pl_function", "comp_optsect", "comp_options", "comp_option", 
  "opt_semi", "pl_block", "decl_sect", "decl_start", "decl_stmts", 
  "decl_stmt", "decl_statement", "@1", "decl_cursor_query", 
  "decl_cursor_args", "decl_cursor_arglist", "decl_cursor_arg", 
  "decl_is_from", "decl_aliasitem", "decl_varname", "decl_renname", 
  "decl_const", "decl_datatype", "decl_notnull", "decl_defval", 
  "decl_defkey", "proc_sect", "proc_stmts", "proc_stmt", "stmt_perform", 
  "stmt_assign", "stmt_getdiag", "getdiag_list", "getdiag_list_item", 
  "getdiag_kind", "getdiag_target", "assign_var", "stmt_if", "stmt_else", 
  "stmt_loop", "stmt_while", "stmt_for", "for_control", "for_variable", 
  "stmt_select", "stmt_exit", "exit_type", "stmt_return", 
  "stmt_return_next", "stmt_raise", "raise_msg", "raise_level", 
  "loop_body", "stmt_execsql", "stmt_dynexecute", "stmt_open", 
  "stmt_fetch", "stmt_close", "stmt_null", "cursor_varptr", 
  "cursor_variable", "execsql_start", "exception_sect", "@2", 
  "proc_exceptions", "proc_exception", "proc_conditions", 
  "expr_until_semi", "expr_until_rightbracket", "expr_until_then", 
  "expr_until_loop", "opt_block_label", "opt_label", "opt_exitcond", 
  "opt_lblname", "lno", 0
};
#endif

# ifdef PLPGSQL_YYPRINT
/* PLPGSQL_YYTOKNUM[PLPGSQL_YYLEX-NUM] -- Internal token number corresponding to
   token PLPGSQL_YYLEX-NUM.  */
static const unsigned short plpgsql_yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284,
     285,   286,   287,   288,   289,   290,   291,   292,   293,   294,
     295,   296,   297,   298,   299,   300,   301,   302,   303,   304,
     305,   306,   307,   308,   309,   310,   311,   312,   313,   314,
     315,   316,   317,   318,   319,   320,    59,    60,    62,    40,
      41,    44,    91
};
# endif

/* PLPGSQL_YYR1[PLPGSQL_YYN] -- Symbol number of symbol that rule PLPGSQL_YYN derives.  */
static const unsigned char plpgsql_yyr1[] =
{
       0,    73,    74,    74,    75,    75,    76,    76,    77,    78,
      78,    79,    80,    80,    80,    81,    82,    82,    83,    83,
      83,    84,    84,    84,    85,    84,    86,    87,    87,    88,
      88,    89,    90,    90,    91,    92,    93,    94,    94,    95,
      96,    96,    97,    97,    98,    98,    99,    99,   100,   100,
     101,   101,   101,   101,   101,   101,   101,   101,   101,   101,
     101,   101,   101,   101,   101,   101,   101,   101,   101,   102,
     103,   104,   105,   105,   106,   107,   107,   108,   109,   109,
     109,   109,   110,   111,   111,   111,   112,   113,   114,   115,
     116,   116,   116,   116,   117,   118,   119,   119,   120,   121,
     122,   123,   124,   124,   124,   124,   124,   124,   125,   126,
     127,   128,   129,   130,   131,   132,   133,   134,   134,   135,
     136,   135,   137,   137,   138,   139,   139,   140,   141,   142,
     143,   144,   144,   145,   145,   145,   146,   146,   147,   148
};

/* PLPGSQL_YYR2[PLPGSQL_YYN] -- Number of symbols composing right hand side of rule PLPGSQL_YYN.  */
static const unsigned char plpgsql_yyr2[] =
{
       0,     2,     4,     4,     0,     1,     2,     1,     2,     0,
       1,     7,     1,     2,     3,     1,     2,     1,     5,     1,
       1,     5,     5,     5,     0,     6,     0,     0,     3,     1,
       3,     2,     1,     1,     1,     1,     1,     0,     1,     0,
       0,     2,     1,     1,     1,     1,     0,     1,     2,     1,
       2,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     3,
       4,     5,     3,     1,     3,     1,     1,     1,     1,     1,
       1,     3,     8,     0,     5,     2,     4,     5,     4,     3,
       1,     1,     1,     1,     2,     4,     1,     1,     2,     2,
       4,     1,     1,     1,     1,     1,     1,     1,     5,     2,
       2,     3,     4,     4,     2,     1,     1,     1,     1,     0,
       0,     4,     2,     1,     5,     3,     1,     0,     0,     0,
       0,     0,     5,     0,     1,     1,     1,     2,     1,     0
};

/* PLPGSQL_YYDEFACT[STATE-NAME] -- Default rule to reduce with in state
   STATE-NUM when PLPGSQL_YYTABLE doesn't specify something else to do.  Zero
   means the default is an error.  */
static const unsigned char plpgsql_yydefact[] =
{
       0,     4,     4,     0,     0,   131,     5,     7,   131,     1,
       8,     0,     9,     0,    12,     6,     9,     0,    10,     2,
     139,    15,    13,     3,   138,     0,   131,    19,     0,    35,
       0,    14,    17,    20,    37,     0,   139,    97,   139,    96,
     139,     0,   139,     0,   139,   139,   139,   139,   139,   139,
      78,    79,    80,   117,   118,     0,   119,    47,    49,    63,
      51,    64,   139,    52,    53,    54,    55,    56,    57,   139,
      58,    59,    60,    61,    62,    65,    66,    67,    68,   139,
      12,    36,     0,     0,    16,     0,    38,    24,    39,   132,
       0,   110,     0,   139,   129,   114,     0,   127,     0,    98,
      99,    94,    50,   139,     0,    48,   128,     0,   133,   109,
     139,   139,   139,     0,     0,     0,    27,    40,   116,     0,
       0,     0,   131,   115,   111,    69,   107,   102,   105,   106,
     104,   103,     0,   120,   133,    81,   127,   134,   135,     0,
     131,     0,   131,   130,     0,     0,    34,     0,     0,     0,
       0,     0,   113,   112,    77,     0,    73,     0,    83,   101,
     100,     0,    11,    70,   127,   136,    95,     0,    88,    90,
      93,    92,    91,     0,    86,   131,    23,    18,    22,     0,
      29,    39,    33,    32,    26,    41,    44,    45,    42,    21,
      43,    71,     0,     0,   131,   139,     0,   139,   121,   123,
     137,     0,    89,    87,    28,     0,    31,    25,    72,    75,
      76,    74,    85,   129,     0,     0,   122,   133,    30,   131,
       0,     0,   126,     0,    83,    82,     0,   131,   108,    84,
     125,   124
};

/* PLPGSQL_YYDEFGOTO[NTERM-NUM]. */
static const short plpgsql_yydefgoto[] =
{
      -1,     3,     5,     6,     7,    19,    55,    13,    22,    31,
      32,    33,   116,   207,   149,   179,   180,   184,   147,    34,
      82,    88,   117,   151,   189,   190,   167,    57,    58,    59,
      60,    61,   155,   156,   211,   157,    62,    63,   196,    64,
      65,    66,   140,   173,    67,    68,    69,    70,    71,    72,
     160,   132,   168,    73,    74,    75,    76,    77,    78,   124,
     119,    79,   104,   161,   198,   199,   221,   125,   135,   122,
     175,    80,   139,   166,    25,    26
};

/* PLPGSQL_YYPACT[STATE-NUM] -- Index in PLPGSQL_YYTABLE of the portion describing
   STATE-NUM.  */
#define PLPGSQL_YYPACT_NINF -143
static const short plpgsql_yypact[] =
{
     -29,   -31,   -31,    51,   -10,    -6,   -31,  -143,    -6,  -143,
    -143,     7,     3,    80,    75,  -143,     3,    26,  -143,  -143,
    -143,  -143,     4,  -143,  -143,    21,   217,  -143,    29,  -143,
      25,     4,  -143,  -143,    45,    30,  -143,  -143,  -143,  -143,
    -143,    87,  -143,    27,  -143,  -143,  -143,  -143,  -143,  -143,
    -143,  -143,  -143,  -143,  -143,    38,    83,    59,  -143,  -143,
    -143,  -143,    34,  -143,  -143,  -143,  -143,  -143,  -143,  -143,
    -143,  -143,  -143,  -143,  -143,  -143,  -143,  -143,  -143,  -143,
       5,  -143,    62,    26,  -143,    92,  -143,  -143,  -143,  -143,
      57,  -143,    57,  -143,  -143,  -143,    58,  -143,    12,  -143,
    -143,  -143,  -143,  -143,   102,  -143,  -143,   116,   -12,  -143,
    -143,  -143,  -143,    29,    55,    63,    60,    91,  -143,    61,
     100,    73,   159,  -143,  -143,  -143,  -143,  -143,  -143,  -143,
    -143,  -143,    76,  -143,   -12,  -143,  -143,  -143,  -143,   -34,
     333,    50,   333,  -143,    66,    65,  -143,    69,    74,     8,
     103,    16,  -143,  -143,  -143,   -48,  -143,   133,    44,  -143,
    -143,    88,  -143,  -143,  -143,  -143,  -143,   123,  -143,  -143,
    -143,  -143,  -143,   115,  -143,   333,  -143,  -143,  -143,     2,
    -143,  -143,  -143,  -143,  -143,  -143,  -143,  -143,  -143,  -143,
    -143,  -143,    73,    -4,   333,  -143,   125,  -143,    88,  -143,
    -143,   112,  -143,  -143,  -143,    74,  -143,  -143,  -143,  -143,
    -143,  -143,  -143,  -143,   119,    26,  -143,   -12,  -143,   159,
      81,   -16,  -143,    82,    44,  -143,    26,   275,  -143,  -143,
    -143,  -143
};

/* PLPGSQL_YYPGOTO[NTERM-NUM].  */
static const short plpgsql_yypgoto[] =
{
    -143,  -143,   144,  -143,   143,   134,    35,  -143,  -143,  -143,
     120,  -143,  -143,  -143,  -143,  -143,   -53,  -143,  -143,  -142,
      40,  -143,   -27,  -143,  -143,  -143,   -26,  -143,    98,  -143,
    -143,  -143,  -143,   -36,  -143,  -143,  -143,  -143,   -67,  -143,
    -143,  -143,  -143,  -143,  -143,  -143,  -143,  -143,  -143,  -143,
    -143,  -143,  -134,  -143,  -143,  -143,  -143,  -143,  -143,  -143,
      67,  -143,  -143,  -143,  -143,   -40,  -143,  -117,  -143,   -52,
    -143,    48,  -130,  -143,   -81,   -35
};

/* PLPGSQL_YYTABLE[PLPGSQL_YYPACT[STATE-NUM]].  What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule which
   number is the opposite.  If zero, do what PLPGSQL_YYDEFACT says.
   If PLPGSQL_YYTABLE_NINF, syntax error.  */
#define PLPGSQL_YYTABLE_NINF -132
static const short plpgsql_yytable[] =
{
      56,    90,   114,    91,   162,    92,   181,    94,   174,    96,
      97,    98,    99,   100,   101,    27,    21,   164,   191,   163,
     186,   226,   126,   192,     1,     2,   110,   107,   187,   182,
     127,   227,   165,     4,   108,   209,   111,   183,   210,   128,
      12,   203,   129,    16,   109,    28,   130,   200,    85,   137,
     138,     9,    86,    14,    87,    10,    14,   112,   121,   194,
     195,    11,   131,   181,  -131,    36,    29,    37,   133,    18,
    -131,    30,   204,   205,    17,   141,   142,   143,    38,    39,
    -131,    40,   188,    41,    42,    20,    21,   223,    24,    35,
    -131,    81,    83,    95,    43,    44,   158,    45,    89,    46,
      93,   103,    47,    48,   102,    49,   106,   169,   170,   171,
     113,  -131,   172,   115,   118,   123,    50,    51,    52,   134,
     136,    53,    54,   145,   150,   146,    11,   152,   153,   148,
     154,   159,   176,   177,   222,   178,    29,   193,   185,   197,
     201,   202,   214,   217,   220,   230,     8,   225,   228,    15,
      23,    84,   218,   144,   206,   105,   208,   229,   216,   120,
     213,   219,   215,     0,     0,    36,     0,    37,   212,     0,
       0,     0,     0,     0,   -46,   -46,   -46,     0,    38,    39,
       0,    40,     0,    41,    42,     0,     0,     0,     0,     0,
       0,     0,     0,   224,    43,    44,     0,    45,     0,    46,
       0,   231,    47,    48,     0,    49,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,    50,    51,    52,     0,
       0,    53,    54,    36,     0,    37,    11,     0,     0,     0,
       0,     0,     0,     0,   -46,   -46,    38,    39,     0,    40,
       0,    41,    42,     0,     0,     0,     0,     0,     0,     0,
       0,     0,    43,    44,     0,    45,     0,    46,     0,     0,
      47,    48,     0,    49,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,    50,    51,    52,     0,     0,    53,
      54,    36,     0,    37,    11,     0,     0,     0,     0,     0,
       0,     0,   -46,     0,    38,    39,     0,    40,     0,    41,
      42,     0,     0,     0,     0,     0,     0,     0,     0,     0,
      43,    44,     0,    45,     0,    46,     0,     0,    47,    48,
       0,    49,     0,     0,     0,     0,   -46,     0,     0,     0,
       0,     0,    50,    51,    52,     0,     0,    53,    54,    36,
       0,    37,    11,     0,     0,     0,     0,     0,     0,     0,
     -46,     0,    38,    39,     0,    40,     0,    41,    42,     0,
       0,     0,     0,     0,     0,     0,     0,     0,    43,    44,
       0,    45,     0,    46,     0,     0,    47,    48,     0,    49,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
      50,    51,    52,     0,     0,    53,    54,     0,     0,     0,
      11
};

static const short plpgsql_yycheck[] =
{
      26,    36,    83,    38,   134,    40,   148,    42,   142,    44,
      45,    46,    47,    48,    49,    11,    11,    51,    66,   136,
       4,    37,    10,    71,    53,    54,    21,    62,    12,    21,
      18,    47,    66,    64,    69,    39,    31,    29,    42,    27,
       5,   175,    30,     8,    79,    41,    34,   164,     3,    61,
      62,     0,     7,     5,     9,    65,     8,    52,    93,    15,
      16,    67,    50,   205,     5,     6,    62,     8,   103,    66,
      11,    67,    70,    71,    67,   110,   111,   112,    19,    20,
      21,    22,    66,    24,    25,     5,    11,   217,    62,    68,
      31,    62,    67,    66,    35,    36,   122,    38,    68,    40,
      13,    18,    43,    44,    66,    46,    72,    57,    58,    59,
      48,    52,    62,    21,    57,    57,    57,    58,    59,    17,
       4,    62,    63,    68,    33,    62,    67,    66,    28,    69,
      57,    55,    66,    68,   215,    66,    62,     4,    35,    51,
      17,    26,    17,    31,    25,   226,     2,    66,    66,     6,
      16,    31,   205,   113,   181,    57,   192,   224,   198,    92,
     195,   213,   197,    -1,    -1,     6,    -1,     8,   194,    -1,
      -1,    -1,    -1,    -1,    15,    16,    17,    -1,    19,    20,
      -1,    22,    -1,    24,    25,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   219,    35,    36,    -1,    38,    -1,    40,
      -1,   227,    43,    44,    -1,    46,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    57,    58,    59,    -1,
      -1,    62,    63,     6,    -1,     8,    67,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    17,    18,    19,    20,    -1,    22,
      -1,    24,    25,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    35,    36,    -1,    38,    -1,    40,    -1,    -1,
      43,    44,    -1,    46,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    57,    58,    59,    -1,    -1,    62,
      63,     6,    -1,     8,    67,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    17,    -1,    19,    20,    -1,    22,    -1,    24,
      25,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      35,    36,    -1,    38,    -1,    40,    -1,    -1,    43,    44,
      -1,    46,    -1,    -1,    -1,    -1,    51,    -1,    -1,    -1,
      -1,    -1,    57,    58,    59,    -1,    -1,    62,    63,     6,
      -1,     8,    67,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      17,    -1,    19,    20,    -1,    22,    -1,    24,    25,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    35,    36,
      -1,    38,    -1,    40,    -1,    -1,    43,    44,    -1,    46,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      57,    58,    59,    -1,    -1,    62,    63,    -1,    -1,    -1,
      67
};

/* PLPGSQL_YYSTOS[STATE-NUM] -- The (internal number of the) accessing
   symbol of state STATE-NUM.  */
static const unsigned char plpgsql_yystos[] =
{
       0,    53,    54,    74,    64,    75,    76,    77,    75,     0,
      65,    67,    79,    80,   144,    77,    79,    67,    66,    78,
       5,    11,    81,    78,    62,   147,   148,    11,    41,    62,
      67,    82,    83,    84,    92,    68,     6,     8,    19,    20,
      22,    24,    25,    35,    36,    38,    40,    43,    44,    46,
      57,    58,    59,    62,    63,    79,    99,   100,   101,   102,
     103,   104,   109,   110,   112,   113,   114,   117,   118,   119,
     120,   121,   122,   126,   127,   128,   129,   130,   131,   134,
     144,    62,    93,    67,    83,     3,     7,     9,    94,    68,
     148,   148,   148,    13,   148,    66,   148,   148,   148,   148,
     148,   148,    66,    18,   135,   101,    72,   148,   148,   148,
      21,    31,    52,    48,   147,    21,    85,    95,    57,   133,
     133,   148,   142,    57,   132,   140,    10,    18,    27,    30,
      34,    50,   124,   148,    17,   141,     4,    61,    62,   145,
     115,   148,   148,   148,    93,    68,    62,    91,    69,    87,
      33,    96,    66,    28,    57,   105,   106,   108,    99,    55,
     123,   136,   145,   140,    51,    66,   146,    99,   125,    57,
      58,    59,    62,   116,   125,   143,    66,    68,    66,    88,
      89,    92,    21,    29,    90,    35,     4,    12,    66,    97,
      98,    66,    71,     4,    15,    16,   111,    51,   137,   138,
     140,    17,    26,   125,    70,    71,    95,    86,   106,    39,
      42,   107,    99,   148,    17,   148,   138,    31,    89,   142,
      25,   139,   147,   145,    99,    66,    37,    47,    66,   111,
     147,    99
};

#if ! defined (PLPGSQL_YYSIZE_T) && defined (__SIZE_TYPE__)
# define PLPGSQL_YYSIZE_T __SIZE_TYPE__
#endif
#if ! defined (PLPGSQL_YYSIZE_T) && defined (size_t)
# define PLPGSQL_YYSIZE_T size_t
#endif
#if ! defined (PLPGSQL_YYSIZE_T)
# if defined (__STDC__) || defined (__cplusplus)
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define PLPGSQL_YYSIZE_T size_t
# endif
#endif
#if ! defined (PLPGSQL_YYSIZE_T)
# define PLPGSQL_YYSIZE_T unsigned int
#endif

#define plpgsql_yyerrok		(plpgsql_yyerrstatus = 0)
#define plpgsql_yyclearin	(plpgsql_yychar = PLPGSQL_YYEMPTY)
#define PLPGSQL_YYEMPTY		(-2)
#define PLPGSQL_YYEOF		0

#define PLPGSQL_YYACCEPT	goto plpgsql_yyacceptlab
#define PLPGSQL_YYABORT		goto plpgsql_yyabortlab
#define PLPGSQL_YYERROR		goto plpgsql_yyerrlab1

/* Like PLPGSQL_YYERROR except do call plpgsql_yyerror.  This remains here temporarily
   to ease the transition to the new meaning of PLPGSQL_YYERROR, for GCC.
   Once GCC version 2 has supplanted version 1, this can go.  */

#define PLPGSQL_YYFAIL		goto plpgsql_yyerrlab

#define PLPGSQL_YYRECOVERING()  (!!plpgsql_yyerrstatus)

#define PLPGSQL_YYBACKUP(Token, Value)					\
do								\
  if (plpgsql_yychar == PLPGSQL_YYEMPTY && plpgsql_yylen == 1)				\
    {								\
      plpgsql_yychar = (Token);						\
      plpgsql_yylval = (Value);						\
      plpgsql_yytoken = PLPGSQL_YYTRANSLATE (plpgsql_yychar);				\
      PLPGSQL_YYPOPSTACK;						\
      goto plpgsql_yybackup;						\
    }								\
  else								\
    { 								\
      plpgsql_yyerror ("syntax error: cannot back up");\
      PLPGSQL_YYERROR;							\
    }								\
while (0)

#define PLPGSQL_YYTERROR	1
#define PLPGSQL_YYERRCODE	256

/* PLPGSQL_YYLLOC_DEFAULT -- Compute the default location (before the actions
   are run).  */

#ifndef PLPGSQL_YYLLOC_DEFAULT
# define PLPGSQL_YYLLOC_DEFAULT(Current, Rhs, N)         \
  Current.first_line   = Rhs[1].first_line;      \
  Current.first_column = Rhs[1].first_column;    \
  Current.last_line    = Rhs[N].last_line;       \
  Current.last_column  = Rhs[N].last_column;
#endif

/* PLPGSQL_YYLEX -- calling `plpgsql_yylex' with the right arguments.  */

#ifdef PLPGSQL_YYLEX_PARAM
# define PLPGSQL_YYLEX plpgsql_yylex (PLPGSQL_YYLEX_PARAM)
#else
# define PLPGSQL_YYLEX plpgsql_yylex ()
#endif

/* Enable debugging if requested.  */
#if PLPGSQL_YYDEBUG

# ifndef PLPGSQL_YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define PLPGSQL_YYFPRINTF fprintf
# endif

# define PLPGSQL_YYDPRINTF(Args)			\
do {						\
  if (plpgsql_yydebug)					\
    PLPGSQL_YYFPRINTF Args;				\
} while (0)

# define PLPGSQL_YYDSYMPRINT(Args)			\
do {						\
  if (plpgsql_yydebug)					\
    plpgsql_yysymprint Args;				\
} while (0)

# define PLPGSQL_YYDSYMPRINTF(Title, Token, Value, Location)		\
do {								\
  if (plpgsql_yydebug)							\
    {								\
      PLPGSQL_YYFPRINTF (stderr, "%s ", Title);				\
      plpgsql_yysymprint (stderr, 					\
                  Token, Value);	\
      PLPGSQL_YYFPRINTF (stderr, "\n");					\
    }								\
} while (0)

/*------------------------------------------------------------------.
| plpgsql_yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (cinluded).                                                   |
`------------------------------------------------------------------*/

#if defined (__STDC__) || defined (__cplusplus)
static void
plpgsql_yy_stack_print (short *bottom, short *top)
#else
static void
plpgsql_yy_stack_print (bottom, top)
    short *bottom;
    short *top;
#endif
{
  PLPGSQL_YYFPRINTF (stderr, "Stack now");
  for (/* Nothing. */; bottom <= top; ++bottom)
    PLPGSQL_YYFPRINTF (stderr, " %d", *bottom);
  PLPGSQL_YYFPRINTF (stderr, "\n");
}

# define PLPGSQL_YY_STACK_PRINT(Bottom, Top)				\
do {								\
  if (plpgsql_yydebug)							\
    plpgsql_yy_stack_print ((Bottom), (Top));				\
} while (0)


/*------------------------------------------------.
| Report that the PLPGSQL_YYRULE is going to be reduced.  |
`------------------------------------------------*/

#if defined (__STDC__) || defined (__cplusplus)
static void
plpgsql_yy_reduce_print (int plpgsql_yyrule)
#else
static void
plpgsql_yy_reduce_print (plpgsql_yyrule)
    int plpgsql_yyrule;
#endif
{
  int plpgsql_yyi;
  unsigned int plpgsql_yylineno = plpgsql_yyrline[plpgsql_yyrule];
  PLPGSQL_YYFPRINTF (stderr, "Reducing stack by rule %d (line %u), ",
             plpgsql_yyrule - 1, plpgsql_yylineno);
  /* Print the symbols being reduced, and their result.  */
  for (plpgsql_yyi = plpgsql_yyprhs[plpgsql_yyrule]; 0 <= plpgsql_yyrhs[plpgsql_yyi]; plpgsql_yyi++)
    PLPGSQL_YYFPRINTF (stderr, "%s ", plpgsql_yytname [plpgsql_yyrhs[plpgsql_yyi]]);
  PLPGSQL_YYFPRINTF (stderr, "-> %s\n", plpgsql_yytname [plpgsql_yyr1[plpgsql_yyrule]]);
}

# define PLPGSQL_YY_REDUCE_PRINT(Rule)		\
do {					\
  if (plpgsql_yydebug)				\
    plpgsql_yy_reduce_print (Rule);		\
} while (0)

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int plpgsql_yydebug;
#else /* !PLPGSQL_YYDEBUG */
# define PLPGSQL_YYDPRINTF(Args)
# define PLPGSQL_YYDSYMPRINT(Args)
# define PLPGSQL_YYDSYMPRINTF(Title, Token, Value, Location)
# define PLPGSQL_YY_STACK_PRINT(Bottom, Top)
# define PLPGSQL_YY_REDUCE_PRINT(Rule)
#endif /* !PLPGSQL_YYDEBUG */


/* PLPGSQL_YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef	PLPGSQL_YYINITDEPTH
# define PLPGSQL_YYINITDEPTH 200
#endif

/* PLPGSQL_YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   SIZE_MAX < PLPGSQL_YYSTACK_BYTES (PLPGSQL_YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#if PLPGSQL_YYMAXDEPTH == 0
# undef PLPGSQL_YYMAXDEPTH
#endif

#ifndef PLPGSQL_YYMAXDEPTH
# define PLPGSQL_YYMAXDEPTH 10000
#endif



#if PLPGSQL_YYERROR_VERBOSE

# ifndef plpgsql_yystrlen
#  if defined (__GLIBC__) && defined (_STRING_H)
#   define plpgsql_yystrlen strlen
#  else
/* Return the length of PLPGSQL_YYSTR.  */
static PLPGSQL_YYSIZE_T
#   if defined (__STDC__) || defined (__cplusplus)
plpgsql_yystrlen (const char *plpgsql_yystr)
#   else
plpgsql_yystrlen (plpgsql_yystr)
     const char *plpgsql_yystr;
#   endif
{
  register const char *plpgsql_yys = plpgsql_yystr;

  while (*plpgsql_yys++ != '\0')
    continue;

  return plpgsql_yys - plpgsql_yystr - 1;
}
#  endif
# endif

# ifndef plpgsql_yystpcpy
#  if defined (__GLIBC__) && defined (_STRING_H) && defined (_GNU_SOURCE)
#   define plpgsql_yystpcpy stpcpy
#  else
/* Copy PLPGSQL_YYSRC to PLPGSQL_YYDEST, returning the address of the terminating '\0' in
   PLPGSQL_YYDEST.  */
static char *
#   if defined (__STDC__) || defined (__cplusplus)
plpgsql_yystpcpy (char *plpgsql_yydest, const char *plpgsql_yysrc)
#   else
plpgsql_yystpcpy (plpgsql_yydest, plpgsql_yysrc)
     char *plpgsql_yydest;
     const char *plpgsql_yysrc;
#   endif
{
  register char *plpgsql_yyd = plpgsql_yydest;
  register const char *plpgsql_yys = plpgsql_yysrc;

  while ((*plpgsql_yyd++ = *plpgsql_yys++) != '\0')
    continue;

  return plpgsql_yyd - 1;
}
#  endif
# endif

#endif /* !PLPGSQL_YYERROR_VERBOSE */



#if PLPGSQL_YYDEBUG
/*--------------------------------.
| Print this symbol on PLPGSQL_YYOUTPUT.  |
`--------------------------------*/

#if defined (__STDC__) || defined (__cplusplus)
static void
plpgsql_yysymprint (FILE *plpgsql_yyoutput, int plpgsql_yytype, PLPGSQL_YYSTYPE *plpgsql_yyvaluep)
#else
static void
plpgsql_yysymprint (plpgsql_yyoutput, plpgsql_yytype, plpgsql_yyvaluep)
    FILE *plpgsql_yyoutput;
    int plpgsql_yytype;
    PLPGSQL_YYSTYPE *plpgsql_yyvaluep;
#endif
{
  /* Pacify ``unused variable'' warnings.  */
  (void) plpgsql_yyvaluep;

  if (plpgsql_yytype < PLPGSQL_YYNTOKENS)
    {
      PLPGSQL_YYFPRINTF (plpgsql_yyoutput, "token %s (", plpgsql_yytname[plpgsql_yytype]);
# ifdef PLPGSQL_YYPRINT
      PLPGSQL_YYPRINT (plpgsql_yyoutput, plpgsql_yytoknum[plpgsql_yytype], *plpgsql_yyvaluep);
# endif
    }
  else
    PLPGSQL_YYFPRINTF (plpgsql_yyoutput, "nterm %s (", plpgsql_yytname[plpgsql_yytype]);

  switch (plpgsql_yytype)
    {
      default:
        break;
    }
  PLPGSQL_YYFPRINTF (plpgsql_yyoutput, ")");
}

#endif /* ! PLPGSQL_YYDEBUG */
/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

#if defined (__STDC__) || defined (__cplusplus)
static void
plpgsql_yydestruct (int plpgsql_yytype, PLPGSQL_YYSTYPE *plpgsql_yyvaluep)
#else
static void
plpgsql_yydestruct (plpgsql_yytype, plpgsql_yyvaluep)
    int plpgsql_yytype;
    PLPGSQL_YYSTYPE *plpgsql_yyvaluep;
#endif
{
  /* Pacify ``unused variable'' warnings.  */
  (void) plpgsql_yyvaluep;

  switch (plpgsql_yytype)
    {

      default:
        break;
    }
}


/* Prevent warnings from -Wmissing-prototypes.  */

#ifdef PLPGSQL_YYPARSE_PARAM
# if defined (__STDC__) || defined (__cplusplus)
int plpgsql_yyparse (void *PLPGSQL_YYPARSE_PARAM);
# else
int plpgsql_yyparse ();
# endif
#else /* ! PLPGSQL_YYPARSE_PARAM */
#if defined (__STDC__) || defined (__cplusplus)
int plpgsql_yyparse (void);
#else
int plpgsql_yyparse ();
#endif
#endif /* ! PLPGSQL_YYPARSE_PARAM */



/* The lookahead symbol.  */
int plpgsql_yychar;

/* The semantic value of the lookahead symbol.  */
PLPGSQL_YYSTYPE plpgsql_yylval;

/* Number of syntax errors so far.  */
int plpgsql_yynerrs;



/*----------.
| plpgsql_yyparse.  |
`----------*/

#ifdef PLPGSQL_YYPARSE_PARAM
# if defined (__STDC__) || defined (__cplusplus)
int plpgsql_yyparse (void *PLPGSQL_YYPARSE_PARAM)
# else
int plpgsql_yyparse (PLPGSQL_YYPARSE_PARAM)
  void *PLPGSQL_YYPARSE_PARAM;
# endif
#else /* ! PLPGSQL_YYPARSE_PARAM */
#if defined (__STDC__) || defined (__cplusplus)
int
plpgsql_yyparse (void)
#else
int
plpgsql_yyparse ()

#endif
#endif
{
  
  register int plpgsql_yystate;
  register int plpgsql_yyn;
  int plpgsql_yyresult;
  /* Number of tokens to shift before error messages enabled.  */
  int plpgsql_yyerrstatus;
  /* Lookahead token as an internal (translated) token number.  */
  int plpgsql_yytoken = 0;

  /* Three stacks and their tools:
     `plpgsql_yyss': related to states,
     `plpgsql_yyvs': related to semantic values,
     `plpgsql_yyls': related to locations.

     Refer to the stacks thru separate pointers, to allow plpgsql_yyoverflow
     to reallocate them elsewhere.  */

  /* The state stack.  */
  short	plpgsql_yyssa[PLPGSQL_YYINITDEPTH];
  short *plpgsql_yyss = plpgsql_yyssa;
  register short *plpgsql_yyssp;

  /* The semantic value stack.  */
  PLPGSQL_YYSTYPE plpgsql_yyvsa[PLPGSQL_YYINITDEPTH];
  PLPGSQL_YYSTYPE *plpgsql_yyvs = plpgsql_yyvsa;
  register PLPGSQL_YYSTYPE *plpgsql_yyvsp;



#define PLPGSQL_YYPOPSTACK   (plpgsql_yyvsp--, plpgsql_yyssp--)

  PLPGSQL_YYSIZE_T plpgsql_yystacksize = PLPGSQL_YYINITDEPTH;

  /* The variables used to return semantic value and location from the
     action routines.  */
  PLPGSQL_YYSTYPE plpgsql_yyval;


  /* When reducing, the number of symbols on the RHS of the reduced
     rule.  */
  int plpgsql_yylen;

  PLPGSQL_YYDPRINTF ((stderr, "Starting parse\n"));

  plpgsql_yystate = 0;
  plpgsql_yyerrstatus = 0;
  plpgsql_yynerrs = 0;
  plpgsql_yychar = PLPGSQL_YYEMPTY;		/* Cause a token to be read.  */

  /* Initialize stack pointers.
     Waste one element of value and location stack
     so that they stay on the same level as the state stack.
     The wasted elements are never initialized.  */

  plpgsql_yyssp = plpgsql_yyss;
  plpgsql_yyvsp = plpgsql_yyvs;

  goto plpgsql_yysetstate;

/*------------------------------------------------------------.
| plpgsql_yynewstate -- Push a new state, which is found in plpgsql_yystate.  |
`------------------------------------------------------------*/
 plpgsql_yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed. so pushing a state here evens the stacks.
     */
  plpgsql_yyssp++;

 plpgsql_yysetstate:
  *plpgsql_yyssp = plpgsql_yystate;

  if (plpgsql_yyss + plpgsql_yystacksize - 1 <= plpgsql_yyssp)
    {
      /* Get the current used size of the three stacks, in elements.  */
      PLPGSQL_YYSIZE_T plpgsql_yysize = plpgsql_yyssp - plpgsql_yyss + 1;

#ifdef plpgsql_yyoverflow
      {
	/* Give user a chance to reallocate the stack. Use copies of
	   these so that the &'s don't force the real ones into
	   memory.  */
	PLPGSQL_YYSTYPE *plpgsql_yyvs1 = plpgsql_yyvs;
	short *plpgsql_yyss1 = plpgsql_yyss;


	/* Each stack pointer address is followed by the size of the
	   data in use in that stack, in bytes.  This used to be a
	   conditional around just the two extra args, but that might
	   be undefined if plpgsql_yyoverflow is a macro.  */
	plpgsql_yyoverflow ("parser stack overflow",
		    &plpgsql_yyss1, plpgsql_yysize * sizeof (*plpgsql_yyssp),
		    &plpgsql_yyvs1, plpgsql_yysize * sizeof (*plpgsql_yyvsp),

		    &plpgsql_yystacksize);

	plpgsql_yyss = plpgsql_yyss1;
	plpgsql_yyvs = plpgsql_yyvs1;
      }
#else /* no plpgsql_yyoverflow */
# ifndef PLPGSQL_YYSTACK_RELOCATE
      goto plpgsql_yyoverflowlab;
# else
      /* Extend the stack our own way.  */
      if (PLPGSQL_YYMAXDEPTH <= plpgsql_yystacksize)
	goto plpgsql_yyoverflowlab;
      plpgsql_yystacksize *= 2;
      if (PLPGSQL_YYMAXDEPTH < plpgsql_yystacksize)
	plpgsql_yystacksize = PLPGSQL_YYMAXDEPTH;

      {
	short *plpgsql_yyss1 = plpgsql_yyss;
	union plpgsql_yyalloc *plpgsql_yyptr =
	  (union plpgsql_yyalloc *) PLPGSQL_YYSTACK_ALLOC (PLPGSQL_YYSTACK_BYTES (plpgsql_yystacksize));
	if (! plpgsql_yyptr)
	  goto plpgsql_yyoverflowlab;
	PLPGSQL_YYSTACK_RELOCATE (plpgsql_yyss);
	PLPGSQL_YYSTACK_RELOCATE (plpgsql_yyvs);

#  undef PLPGSQL_YYSTACK_RELOCATE
	if (plpgsql_yyss1 != plpgsql_yyssa)
	  PLPGSQL_YYSTACK_FREE (plpgsql_yyss1);
      }
# endif
#endif /* no plpgsql_yyoverflow */

      plpgsql_yyssp = plpgsql_yyss + plpgsql_yysize - 1;
      plpgsql_yyvsp = plpgsql_yyvs + plpgsql_yysize - 1;


      PLPGSQL_YYDPRINTF ((stderr, "Stack size increased to %lu\n",
		  (unsigned long int) plpgsql_yystacksize));

      if (plpgsql_yyss + plpgsql_yystacksize - 1 <= plpgsql_yyssp)
	PLPGSQL_YYABORT;
    }

  PLPGSQL_YYDPRINTF ((stderr, "Entering state %d\n", plpgsql_yystate));

  goto plpgsql_yybackup;

/*-----------.
| plpgsql_yybackup.  |
`-----------*/
plpgsql_yybackup:

/* Do appropriate processing given the current state.  */
/* Read a lookahead token if we need one and don't already have one.  */
/* plpgsql_yyresume: */

  /* First try to decide what to do without reference to lookahead token.  */

  plpgsql_yyn = plpgsql_yypact[plpgsql_yystate];
  if (plpgsql_yyn == PLPGSQL_YYPACT_NINF)
    goto plpgsql_yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* PLPGSQL_YYCHAR is either PLPGSQL_YYEMPTY or PLPGSQL_YYEOF or a valid lookahead symbol.  */
  if (plpgsql_yychar == PLPGSQL_YYEMPTY)
    {
      PLPGSQL_YYDPRINTF ((stderr, "Reading a token: "));
      plpgsql_yychar = PLPGSQL_YYLEX;
    }

  if (plpgsql_yychar <= PLPGSQL_YYEOF)
    {
      plpgsql_yychar = plpgsql_yytoken = PLPGSQL_YYEOF;
      PLPGSQL_YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else
    {
      plpgsql_yytoken = PLPGSQL_YYTRANSLATE (plpgsql_yychar);
      PLPGSQL_YYDSYMPRINTF ("Next token is", plpgsql_yytoken, &plpgsql_yylval, &plpgsql_yylloc);
    }

  /* If the proper action on seeing token PLPGSQL_YYTOKEN is to reduce or to
     detect an error, take that action.  */
  plpgsql_yyn += plpgsql_yytoken;
  if (plpgsql_yyn < 0 || PLPGSQL_YYLAST < plpgsql_yyn || plpgsql_yycheck[plpgsql_yyn] != plpgsql_yytoken)
    goto plpgsql_yydefault;
  plpgsql_yyn = plpgsql_yytable[plpgsql_yyn];
  if (plpgsql_yyn <= 0)
    {
      if (plpgsql_yyn == 0 || plpgsql_yyn == PLPGSQL_YYTABLE_NINF)
	goto plpgsql_yyerrlab;
      plpgsql_yyn = -plpgsql_yyn;
      goto plpgsql_yyreduce;
    }

  if (plpgsql_yyn == PLPGSQL_YYFINAL)
    PLPGSQL_YYACCEPT;

  /* Shift the lookahead token.  */
  PLPGSQL_YYDPRINTF ((stderr, "Shifting token %s, ", plpgsql_yytname[plpgsql_yytoken]));

  /* Discard the token being shifted unless it is eof.  */
  if (plpgsql_yychar != PLPGSQL_YYEOF)
    plpgsql_yychar = PLPGSQL_YYEMPTY;

  *++plpgsql_yyvsp = plpgsql_yylval;


  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (plpgsql_yyerrstatus)
    plpgsql_yyerrstatus--;

  plpgsql_yystate = plpgsql_yyn;
  goto plpgsql_yynewstate;


/*-----------------------------------------------------------.
| plpgsql_yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
plpgsql_yydefault:
  plpgsql_yyn = plpgsql_yydefact[plpgsql_yystate];
  if (plpgsql_yyn == 0)
    goto plpgsql_yyerrlab;
  goto plpgsql_yyreduce;


/*-----------------------------.
| plpgsql_yyreduce -- Do a reduction.  |
`-----------------------------*/
plpgsql_yyreduce:
  /* plpgsql_yyn is the number of a rule to reduce with.  */
  plpgsql_yylen = plpgsql_yyr2[plpgsql_yyn];

  /* If PLPGSQL_YYLEN is nonzero, implement the default value of the action:
     `$$ = $1'.

     Otherwise, the following line sets PLPGSQL_YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to PLPGSQL_YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that PLPGSQL_YYVAL may be used uninitialized.  */
  plpgsql_yyval = plpgsql_yyvsp[1-plpgsql_yylen];


  PLPGSQL_YY_REDUCE_PRINT (plpgsql_yyn);
  switch (plpgsql_yyn)
    {
        case 2:
#line 231 "gram.y"
    {
						plpgsql_yylval.program = (PLpgSQL_stmt_block *)plpgsql_yyvsp[-1].stmt;
					}
    break;

  case 3:
#line 235 "gram.y"
    {
						plpgsql_yylval.program = (PLpgSQL_stmt_block *)plpgsql_yyvsp[-1].stmt;
					}
    break;

  case 8:
#line 249 "gram.y"
    {
						plpgsql_DumpExecTree = true;
					}
    break;

  case 11:
#line 259 "gram.y"
    {
						PLpgSQL_stmt_block *new;

						new = palloc0(sizeof(PLpgSQL_stmt_block));

						new->cmd_type	= PLPGSQL_STMT_BLOCK;
						new->lineno		= plpgsql_yyvsp[-4].ival;
						new->label		= plpgsql_yyvsp[-6].declhdr.label;
						new->n_initvars = plpgsql_yyvsp[-6].declhdr.n_initvars;
						new->initvarnos = plpgsql_yyvsp[-6].declhdr.initvarnos;
						new->body		= plpgsql_yyvsp[-3].list;
						new->exceptions	= plpgsql_yyvsp[-2].exception_block;

						check_labels(plpgsql_yyvsp[-6].declhdr.label, plpgsql_yyvsp[0].str);
						plpgsql_ns_pop();

						plpgsql_yyval.stmt = (PLpgSQL_stmt *)new;
					}
    break;

  case 12:
#line 281 "gram.y"
    {
						plpgsql_ns_setlocal(false);
						plpgsql_yyval.declhdr.label	  = plpgsql_yyvsp[0].str;
						plpgsql_yyval.declhdr.n_initvars = 0;
						plpgsql_yyval.declhdr.initvarnos = NULL;
						plpgsql_add_initdatums(NULL);
					}
    break;

  case 13:
#line 289 "gram.y"
    {
						plpgsql_ns_setlocal(false);
						plpgsql_yyval.declhdr.label	  = plpgsql_yyvsp[-1].str;
						plpgsql_yyval.declhdr.n_initvars = 0;
						plpgsql_yyval.declhdr.initvarnos = NULL;
						plpgsql_add_initdatums(NULL);
					}
    break;

  case 14:
#line 297 "gram.y"
    {
						plpgsql_ns_setlocal(false);
						if (plpgsql_yyvsp[0].str != NULL)
							plpgsql_yyval.declhdr.label = plpgsql_yyvsp[0].str;
						else
							plpgsql_yyval.declhdr.label = plpgsql_yyvsp[-2].str;
						plpgsql_yyval.declhdr.n_initvars = plpgsql_add_initdatums(&(plpgsql_yyval.declhdr.initvarnos));
					}
    break;

  case 15:
#line 308 "gram.y"
    {
						plpgsql_ns_setlocal(true);
					}
    break;

  case 16:
#line 314 "gram.y"
    {	plpgsql_yyval.str = plpgsql_yyvsp[0].str;	}
    break;

  case 17:
#line 316 "gram.y"
    {	plpgsql_yyval.str = plpgsql_yyvsp[0].str;	}
    break;

  case 18:
#line 320 "gram.y"
    {	plpgsql_yyval.str = plpgsql_yyvsp[-2].str;	}
    break;

  case 19:
#line 322 "gram.y"
    {	plpgsql_yyval.str = NULL;	}
    break;

  case 20:
#line 324 "gram.y"
    {	plpgsql_yyval.str = NULL;	}
    break;

  case 21:
#line 328 "gram.y"
    {
						PLpgSQL_variable	*var;

						var = plpgsql_build_variable(plpgsql_yyvsp[-4].varname.name, plpgsql_yyvsp[-4].varname.lineno,
													 plpgsql_yyvsp[-2].dtype, true);
						if (plpgsql_yyvsp[-3].boolean)
						{
							if (var->dtype == PLPGSQL_DTYPE_VAR)
								((PLpgSQL_var *) var)->isconst = plpgsql_yyvsp[-3].boolean;
							else
								ereport(ERROR,
										(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
										 errmsg("row or record variable cannot be CONSTANT")));
						}
						if (plpgsql_yyvsp[-1].boolean)
						{
							if (var->dtype == PLPGSQL_DTYPE_VAR)
								((PLpgSQL_var *) var)->notnull = plpgsql_yyvsp[-1].boolean;
							else
								ereport(ERROR,
										(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
										 errmsg("row or record variable cannot be NOT NULL")));
						}
						if (plpgsql_yyvsp[0].expr != NULL)
						{
							if (var->dtype == PLPGSQL_DTYPE_VAR)
								((PLpgSQL_var *) var)->default_val = plpgsql_yyvsp[0].expr;
							else
								ereport(ERROR,
										(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
										 errmsg("default value for row or record variable is not supported")));
						}
					}
    break;

  case 22:
#line 362 "gram.y"
    {
						plpgsql_ns_additem(plpgsql_yyvsp[-1].nsitem->itemtype,
										   plpgsql_yyvsp[-1].nsitem->itemno, plpgsql_yyvsp[-4].varname.name);
					}
    break;

  case 23:
#line 367 "gram.y"
    {
						plpgsql_ns_rename(plpgsql_yyvsp[-3].str, plpgsql_yyvsp[-1].str);
					}
    break;

  case 24:
#line 371 "gram.y"
    { plpgsql_ns_push(NULL); }
    break;

  case 25:
#line 373 "gram.y"
    {
						PLpgSQL_var *new;
						PLpgSQL_expr *curname_def;
						char		buf[1024];
						char		*cp1;
						char		*cp2;

						/* pop local namespace for cursor args */
						plpgsql_ns_pop();

						new = (PLpgSQL_var *)
							plpgsql_build_variable(plpgsql_yyvsp[-5].varname.name, plpgsql_yyvsp[-5].varname.lineno,
												   plpgsql_build_datatype(REFCURSOROID,
																		  -1),
												   true);

						curname_def = palloc0(sizeof(PLpgSQL_expr));

						curname_def->dtype = PLPGSQL_DTYPE_EXPR;
						strcpy(buf, "SELECT ");
						cp1 = new->refname;
						cp2 = buf + strlen(buf);
						if (strchr(cp1, '\\') != NULL)
							*cp2++ = ESCAPE_STRING_SYNTAX;
						*cp2++ = '\'';
						while (*cp1)
						{
							if (SQL_STR_DOUBLE(*cp1))
								*cp2++ = *cp1;
							*cp2++ = *cp1++;
						}
						strcpy(cp2, "'::refcursor");
						curname_def->query = pstrdup(buf);
						new->default_val = curname_def;

						new->cursor_explicit_expr = plpgsql_yyvsp[0].expr;
						if (plpgsql_yyvsp[-2].row == NULL)
							new->cursor_explicit_argrow = -1;
						else
							new->cursor_explicit_argrow = plpgsql_yyvsp[-2].row->rowno;
					}
    break;

  case 26:
#line 417 "gram.y"
    {
						PLpgSQL_expr *query;

						plpgsql_ns_setlocal(false);
						query = read_sql_stmt("");
						plpgsql_ns_setlocal(true);

						plpgsql_yyval.expr = query;
					}
    break;

  case 27:
#line 429 "gram.y"
    {
						plpgsql_yyval.row = NULL;
					}
    break;

  case 28:
#line 433 "gram.y"
    {
						PLpgSQL_row *new;
						int i;
						ListCell *l;

						new = palloc0(sizeof(PLpgSQL_row));
						new->dtype = PLPGSQL_DTYPE_ROW;
						new->lineno = plpgsql_scanner_lineno();
						new->rowtupdesc = NULL;
						new->nfields = list_length(plpgsql_yyvsp[-1].list);
						new->fieldnames = palloc(new->nfields * sizeof(char *));
						new->varnos = palloc(new->nfields * sizeof(int));

						i = 0;
						foreach (l, plpgsql_yyvsp[-1].list)
						{
							PLpgSQL_variable *arg = (PLpgSQL_variable *) lfirst(l);
							new->fieldnames[i] = arg->refname;
							new->varnos[i] = arg->dno;
							i++;
						}
						list_free(plpgsql_yyvsp[-1].list);

						plpgsql_adddatum((PLpgSQL_datum *) new);
						plpgsql_yyval.row = new;
					}
    break;

  case 29:
#line 462 "gram.y"
    {
						plpgsql_yyval.list = list_make1(plpgsql_yyvsp[0].variable);
					}
    break;

  case 30:
#line 466 "gram.y"
    {
						plpgsql_yyval.list = lappend(plpgsql_yyvsp[-2].list, plpgsql_yyvsp[0].variable);
					}
    break;

  case 31:
#line 472 "gram.y"
    {
						plpgsql_yyval.variable = plpgsql_build_variable(plpgsql_yyvsp[-1].varname.name, plpgsql_yyvsp[-1].varname.lineno,
													plpgsql_yyvsp[0].dtype, true);
					}
    break;

  case 34:
#line 482 "gram.y"
    {
						char	*name;
						PLpgSQL_nsitem *nsi;

						plpgsql_convert_ident(plpgsql_yytext, &name, 1);
						if (name[0] != '$')
							plpgsql_yyerror("only positional parameters may be aliased");

						plpgsql_ns_setlocal(false);
						nsi = plpgsql_ns_lookup(name, NULL);
						if (nsi == NULL)
						{
							plpgsql_error_lineno = plpgsql_scanner_lineno();
							ereport(ERROR,
									(errcode(ERRCODE_UNDEFINED_PARAMETER),
									 errmsg("function has no parameter \"%s\"",
											name)));
						}

						plpgsql_ns_setlocal(true);

						pfree(name);

						plpgsql_yyval.nsitem = nsi;
					}
    break;

  case 35:
#line 510 "gram.y"
    {
						char	*name;

						plpgsql_convert_ident(plpgsql_yytext, &name, 1);
						plpgsql_yyval.varname.name = name;
						plpgsql_yyval.varname.lineno  = plpgsql_scanner_lineno();
					}
    break;

  case 36:
#line 520 "gram.y"
    {
						char	*name;

						plpgsql_convert_ident(plpgsql_yytext, &name, 1);
						/* the result must be palloc'd, see plpgsql_ns_rename */
						plpgsql_yyval.str = name;
					}
    break;

  case 37:
#line 530 "gram.y"
    { plpgsql_yyval.boolean = false; }
    break;

  case 38:
#line 532 "gram.y"
    { plpgsql_yyval.boolean = true; }
    break;

  case 39:
#line 536 "gram.y"
    {
						/*
						 * If there's a lookahead token, read_datatype
						 * should consume it.
						 */
						plpgsql_yyval.dtype = read_datatype(plpgsql_yychar);
						plpgsql_yyclearin;
					}
    break;

  case 40:
#line 547 "gram.y"
    { plpgsql_yyval.boolean = false; }
    break;

  case 41:
#line 549 "gram.y"
    { plpgsql_yyval.boolean = true; }
    break;

  case 42:
#line 553 "gram.y"
    { plpgsql_yyval.expr = NULL; }
    break;

  case 43:
#line 555 "gram.y"
    {
						plpgsql_ns_setlocal(false);
						plpgsql_yyval.expr = plpgsql_read_expression(';', ";");
						plpgsql_ns_setlocal(true);
					}
    break;

  case 46:
#line 567 "gram.y"
    {
						plpgsql_yyval.list = NIL;
					}
    break;

  case 47:
#line 571 "gram.y"
    { plpgsql_yyval.list = plpgsql_yyvsp[0].list; }
    break;

  case 48:
#line 575 "gram.y"
    {
							if (plpgsql_yyvsp[0].stmt == NULL)
								plpgsql_yyval.list = plpgsql_yyvsp[-1].list;
							else
								plpgsql_yyval.list = lappend(plpgsql_yyvsp[-1].list, plpgsql_yyvsp[0].stmt);
						}
    break;

  case 49:
#line 582 "gram.y"
    {
							if (plpgsql_yyvsp[0].stmt == NULL)
								plpgsql_yyval.list = NULL;
							else
								plpgsql_yyval.list = list_make1(plpgsql_yyvsp[0].stmt);
						}
    break;

  case 50:
#line 591 "gram.y"
    { plpgsql_yyval.stmt = plpgsql_yyvsp[-1].stmt; }
    break;

  case 51:
#line 593 "gram.y"
    { plpgsql_yyval.stmt = plpgsql_yyvsp[0].stmt; }
    break;

  case 52:
#line 595 "gram.y"
    { plpgsql_yyval.stmt = plpgsql_yyvsp[0].stmt; }
    break;

  case 53:
#line 597 "gram.y"
    { plpgsql_yyval.stmt = plpgsql_yyvsp[0].stmt; }
    break;

  case 54:
#line 599 "gram.y"
    { plpgsql_yyval.stmt = plpgsql_yyvsp[0].stmt; }
    break;

  case 55:
#line 601 "gram.y"
    { plpgsql_yyval.stmt = plpgsql_yyvsp[0].stmt; }
    break;

  case 56:
#line 603 "gram.y"
    { plpgsql_yyval.stmt = plpgsql_yyvsp[0].stmt; }
    break;

  case 57:
#line 605 "gram.y"
    { plpgsql_yyval.stmt = plpgsql_yyvsp[0].stmt; }
    break;

  case 58:
#line 607 "gram.y"
    { plpgsql_yyval.stmt = plpgsql_yyvsp[0].stmt; }
    break;

  case 59:
#line 609 "gram.y"
    { plpgsql_yyval.stmt = plpgsql_yyvsp[0].stmt; }
    break;

  case 60:
#line 611 "gram.y"
    { plpgsql_yyval.stmt = plpgsql_yyvsp[0].stmt; }
    break;

  case 61:
#line 613 "gram.y"
    { plpgsql_yyval.stmt = plpgsql_yyvsp[0].stmt; }
    break;

  case 62:
#line 615 "gram.y"
    { plpgsql_yyval.stmt = plpgsql_yyvsp[0].stmt; }
    break;

  case 63:
#line 617 "gram.y"
    { plpgsql_yyval.stmt = plpgsql_yyvsp[0].stmt; }
    break;

  case 64:
#line 619 "gram.y"
    { plpgsql_yyval.stmt = plpgsql_yyvsp[0].stmt; }
    break;

  case 65:
#line 621 "gram.y"
    { plpgsql_yyval.stmt = plpgsql_yyvsp[0].stmt; }
    break;

  case 66:
#line 623 "gram.y"
    { plpgsql_yyval.stmt = plpgsql_yyvsp[0].stmt; }
    break;

  case 67:
#line 625 "gram.y"
    { plpgsql_yyval.stmt = plpgsql_yyvsp[0].stmt; }
    break;

  case 68:
#line 627 "gram.y"
    { plpgsql_yyval.stmt = plpgsql_yyvsp[0].stmt; }
    break;

  case 69:
#line 631 "gram.y"
    {
						PLpgSQL_stmt_perform *new;

						new = palloc0(sizeof(PLpgSQL_stmt_perform));
						new->cmd_type = PLPGSQL_STMT_PERFORM;
						new->lineno   = plpgsql_yyvsp[-1].ival;
						new->expr  = plpgsql_yyvsp[0].expr;

						plpgsql_yyval.stmt = (PLpgSQL_stmt *)new;
					}
    break;

  case 70:
#line 644 "gram.y"
    {
						PLpgSQL_stmt_assign *new;

						new = palloc0(sizeof(PLpgSQL_stmt_assign));
						new->cmd_type = PLPGSQL_STMT_ASSIGN;
						new->lineno   = plpgsql_yyvsp[-2].ival;
						new->varno = plpgsql_yyvsp[-3].ival;
						new->expr  = plpgsql_yyvsp[0].expr;

						plpgsql_yyval.stmt = (PLpgSQL_stmt *)new;
					}
    break;

  case 71:
#line 658 "gram.y"
    {
						PLpgSQL_stmt_getdiag	 *new;

						new = palloc0(sizeof(PLpgSQL_stmt_getdiag));
						new->cmd_type = PLPGSQL_STMT_GETDIAG;
						new->lineno   = plpgsql_yyvsp[-2].ival;
						new->diag_items  = plpgsql_yyvsp[-1].list;

						plpgsql_yyval.stmt = (PLpgSQL_stmt *)new;
					}
    break;

  case 72:
#line 671 "gram.y"
    {
						plpgsql_yyval.list = lappend(plpgsql_yyvsp[-2].list, plpgsql_yyvsp[0].diagitem);
					}
    break;

  case 73:
#line 675 "gram.y"
    {
						plpgsql_yyval.list = list_make1(plpgsql_yyvsp[0].diagitem);
					}
    break;

  case 74:
#line 681 "gram.y"
    {
						PLpgSQL_diag_item *new;

						new = palloc(sizeof(PLpgSQL_diag_item));
						new->target = plpgsql_yyvsp[-2].ival;
						new->kind = plpgsql_yyvsp[0].ival;

						plpgsql_yyval.diagitem = new;
					}
    break;

  case 75:
#line 693 "gram.y"
    {
						plpgsql_yyval.ival = PLPGSQL_GETDIAG_ROW_COUNT;
					}
    break;

  case 76:
#line 697 "gram.y"
    {
						plpgsql_yyval.ival = PLPGSQL_GETDIAG_RESULT_OID;
					}
    break;

  case 77:
#line 703 "gram.y"
    {
						check_assignable(plpgsql_yylval.scalar);
						plpgsql_yyval.ival = plpgsql_yylval.scalar->dno;
					}
    break;

  case 78:
#line 711 "gram.y"
    {
						check_assignable(plpgsql_yylval.scalar);
						plpgsql_yyval.ival = plpgsql_yylval.scalar->dno;
					}
    break;

  case 79:
#line 716 "gram.y"
    {
						check_assignable((PLpgSQL_datum *) plpgsql_yylval.row);
						plpgsql_yyval.ival = plpgsql_yylval.row->rowno;
					}
    break;

  case 80:
#line 721 "gram.y"
    {
						check_assignable((PLpgSQL_datum *) plpgsql_yylval.rec);
						plpgsql_yyval.ival = plpgsql_yylval.rec->recno;
					}
    break;

  case 81:
#line 726 "gram.y"
    {
						PLpgSQL_arrayelem	*new;

						new = palloc0(sizeof(PLpgSQL_arrayelem));
						new->dtype		= PLPGSQL_DTYPE_ARRAYELEM;
						new->subscript	= plpgsql_yyvsp[0].expr;
						new->arrayparentno = plpgsql_yyvsp[-2].ival;

						plpgsql_adddatum((PLpgSQL_datum *)new);

						plpgsql_yyval.ival = new->dno;
					}
    break;

  case 82:
#line 741 "gram.y"
    {
						PLpgSQL_stmt_if *new;

						new = palloc0(sizeof(PLpgSQL_stmt_if));
						new->cmd_type	= PLPGSQL_STMT_IF;
						new->lineno		= plpgsql_yyvsp[-6].ival;
						new->cond		= plpgsql_yyvsp[-5].expr;
						new->true_body	= plpgsql_yyvsp[-4].list;
						new->false_body = plpgsql_yyvsp[-3].list;

						plpgsql_yyval.stmt = (PLpgSQL_stmt *)new;
					}
    break;

  case 83:
#line 756 "gram.y"
    {
						plpgsql_yyval.list = NIL;
					}
    break;

  case 84:
#line 760 "gram.y"
    {
						/*
						 * Translate the structure:	   into:
						 *
						 * IF c1 THEN				   IF c1 THEN
						 *	 ...						   ...
						 * ELSIF c2 THEN			   ELSE
						 *								   IF c2 THEN
						 *	 ...							   ...
						 * ELSE							   ELSE
						 *	 ...							   ...
						 * END IF						   END IF
						 *							   END IF
						 */
						PLpgSQL_stmt_if *new_if;

						/* first create a new if-statement */
						new_if = palloc0(sizeof(PLpgSQL_stmt_if));
						new_if->cmd_type	= PLPGSQL_STMT_IF;
						new_if->lineno		= plpgsql_yyvsp[-3].ival;
						new_if->cond		= plpgsql_yyvsp[-2].expr;
						new_if->true_body	= plpgsql_yyvsp[-1].list;
						new_if->false_body	= plpgsql_yyvsp[0].list;

						/* wrap the if-statement in a "container" list */
						plpgsql_yyval.list = list_make1(new_if);
					}
    break;

  case 85:
#line 789 "gram.y"
    {
						plpgsql_yyval.list = plpgsql_yyvsp[0].list;
					}
    break;

  case 86:
#line 795 "gram.y"
    {
						PLpgSQL_stmt_loop *new;

						new = palloc0(sizeof(PLpgSQL_stmt_loop));
						new->cmd_type = PLPGSQL_STMT_LOOP;
						new->lineno   = plpgsql_yyvsp[-1].ival;
						new->label	  = plpgsql_yyvsp[-3].str;
						new->body	  = plpgsql_yyvsp[0].loop_body.stmts;

						check_labels(plpgsql_yyvsp[-3].str, plpgsql_yyvsp[0].loop_body.end_label);
						plpgsql_ns_pop();

						plpgsql_yyval.stmt = (PLpgSQL_stmt *)new;
					}
    break;

  case 87:
#line 812 "gram.y"
    {
						PLpgSQL_stmt_while *new;

						new = palloc0(sizeof(PLpgSQL_stmt_while));
						new->cmd_type = PLPGSQL_STMT_WHILE;
						new->lineno   = plpgsql_yyvsp[-2].ival;
						new->label	  = plpgsql_yyvsp[-4].str;
						new->cond	  = plpgsql_yyvsp[-1].expr;
						new->body	  = plpgsql_yyvsp[0].loop_body.stmts;

						check_labels(plpgsql_yyvsp[-4].str, plpgsql_yyvsp[0].loop_body.end_label);
						plpgsql_ns_pop();

						plpgsql_yyval.stmt = (PLpgSQL_stmt *)new;
					}
    break;

  case 88:
#line 830 "gram.y"
    {
						/* This runs after we've scanned the loop body */
						if (plpgsql_yyvsp[-1].stmt->cmd_type == PLPGSQL_STMT_FORI)
						{
							PLpgSQL_stmt_fori		*new;

							new = (PLpgSQL_stmt_fori *) plpgsql_yyvsp[-1].stmt;
							new->label	  = plpgsql_yyvsp[-3].str;
							new->body	  = plpgsql_yyvsp[0].loop_body.stmts;
							plpgsql_yyval.stmt = (PLpgSQL_stmt *) new;
						}
						else if (plpgsql_yyvsp[-1].stmt->cmd_type == PLPGSQL_STMT_FORS)
						{
							PLpgSQL_stmt_fors		*new;

							new = (PLpgSQL_stmt_fors *) plpgsql_yyvsp[-1].stmt;
							new->label	  = plpgsql_yyvsp[-3].str;
							new->body	  = plpgsql_yyvsp[0].loop_body.stmts;
							plpgsql_yyval.stmt = (PLpgSQL_stmt *) new;
						}
						else
						{
							PLpgSQL_stmt_dynfors	*new;

							Assert(plpgsql_yyvsp[-1].stmt->cmd_type == PLPGSQL_STMT_DYNFORS);
							new = (PLpgSQL_stmt_dynfors *) plpgsql_yyvsp[-1].stmt;
							new->label	  = plpgsql_yyvsp[-3].str;
							new->body	  = plpgsql_yyvsp[0].loop_body.stmts;
							plpgsql_yyval.stmt = (PLpgSQL_stmt *) new;
						}

						check_labels(plpgsql_yyvsp[-3].str, plpgsql_yyvsp[0].loop_body.end_label);
						/* close namespace started in opt_label */
						plpgsql_ns_pop();
					}
    break;

  case 89:
#line 869 "gram.y"
    {
						int			tok = plpgsql_yylex();

						/* Simple case: EXECUTE is a dynamic FOR loop */
						if (tok == K_EXECUTE)
						{
							PLpgSQL_stmt_dynfors	*new;
							PLpgSQL_expr			*expr;

							expr = plpgsql_read_expression(K_LOOP, "LOOP");

							new = palloc0(sizeof(PLpgSQL_stmt_dynfors));
							new->cmd_type = PLPGSQL_STMT_DYNFORS;
							new->lineno   = plpgsql_yyvsp[-2].ival;
							if (plpgsql_yyvsp[-1].forvariable.rec)
								new->rec = plpgsql_yyvsp[-1].forvariable.rec;
							else if (plpgsql_yyvsp[-1].forvariable.row)
								new->row = plpgsql_yyvsp[-1].forvariable.row;
							else
							{
								plpgsql_error_lineno = plpgsql_yyvsp[-2].ival;
								plpgsql_yyerror("loop variable of loop over rows must be a record or row variable");
							}
							new->query = expr;

							plpgsql_yyval.stmt = (PLpgSQL_stmt *) new;
						}
						else
						{
							PLpgSQL_expr	*expr1;
							bool			 reverse = false;

							/*
							 * We have to distinguish between two
							 * alternatives: FOR var IN a .. b and FOR
							 * var IN query. Unfortunately this is
							 * tricky, since the query in the second
							 * form needn't start with a SELECT
							 * keyword.  We use the ugly hack of
							 * looking for two periods after the first
							 * token. We also check for the REVERSE
							 * keyword, which means it must be an
							 * integer loop.
							 */
							if (tok == K_REVERSE)
								reverse = true;
							else
								plpgsql_push_back_token(tok);

							/*
							 * Read tokens until we see either a ".."
							 * or a LOOP. The text we read may not
							 * necessarily be a well-formed SQL
							 * statement, so we need to invoke
							 * read_sql_construct directly.
							 */
							expr1 = read_sql_construct(K_DOTDOT,
													   K_LOOP,
													   "LOOP",
													   "SELECT ",
													   true,
													   false,
													   &tok);

							if (tok == K_DOTDOT)
							{
								/* Saw "..", so it must be an integer loop */
								PLpgSQL_expr		*expr2;
								PLpgSQL_var			*fvar;
								PLpgSQL_stmt_fori	*new;

								/* First expression is well-formed */
								check_sql_expr(expr1->query);

								expr2 = plpgsql_read_expression(K_LOOP, "LOOP");

								fvar = (PLpgSQL_var *)
									plpgsql_build_variable(plpgsql_yyvsp[-1].forvariable.name,
														   plpgsql_yyvsp[-1].forvariable.lineno,
														   plpgsql_build_datatype(INT4OID,
																				  -1),
														   true);

								/* put the for-variable into the local block */
								plpgsql_add_initdatums(NULL);

								new = palloc0(sizeof(PLpgSQL_stmt_fori));
								new->cmd_type = PLPGSQL_STMT_FORI;
								new->lineno   = plpgsql_yyvsp[-2].ival;
								new->var	  = fvar;
								new->reverse  = reverse;
								new->lower	  = expr1;
								new->upper	  = expr2;

								plpgsql_yyval.stmt = (PLpgSQL_stmt *) new;
							}
							else
							{
								/*
								 * No "..", so it must be a query loop. We've prefixed an
								 * extra SELECT to the query text, so we need to remove that
								 * before performing syntax checking.
								 */
								char				*tmp_query;
								PLpgSQL_stmt_fors	*new;

								if (reverse)
									plpgsql_yyerror("cannot specify REVERSE in query FOR loop");

								Assert(strncmp(expr1->query, "SELECT ", 7) == 0);
								tmp_query = pstrdup(expr1->query + 7);
								pfree(expr1->query);
								expr1->query = tmp_query;

								check_sql_expr(expr1->query);

								new = palloc0(sizeof(PLpgSQL_stmt_fors));
								new->cmd_type = PLPGSQL_STMT_FORS;
								new->lineno   = plpgsql_yyvsp[-2].ival;
								if (plpgsql_yyvsp[-1].forvariable.rec)
									new->rec = plpgsql_yyvsp[-1].forvariable.rec;
								else if (plpgsql_yyvsp[-1].forvariable.row)
									new->row = plpgsql_yyvsp[-1].forvariable.row;
								else
								{
									plpgsql_error_lineno = plpgsql_yyvsp[-2].ival;
									plpgsql_yyerror("loop variable of loop over rows must be record or row variable");
								}

								new->query = expr1;
								plpgsql_yyval.stmt = (PLpgSQL_stmt *) new;
							}
						}
					}
    break;

  case 90:
#line 1006 "gram.y"
    {
						char		*name;

						plpgsql_convert_ident(plpgsql_yytext, &name, 1);
						plpgsql_yyval.forvariable.name = name;
						plpgsql_yyval.forvariable.lineno  = plpgsql_scanner_lineno();
						plpgsql_yyval.forvariable.rec = NULL;
						plpgsql_yyval.forvariable.row = NULL;
					}
    break;

  case 91:
#line 1016 "gram.y"
    {
						char		*name;

						plpgsql_convert_ident(plpgsql_yytext, &name, 1);
						plpgsql_yyval.forvariable.name = name;
						plpgsql_yyval.forvariable.lineno  = plpgsql_scanner_lineno();
						plpgsql_yyval.forvariable.rec = NULL;
						plpgsql_yyval.forvariable.row = NULL;
					}
    break;

  case 92:
#line 1026 "gram.y"
    {
						char		*name;

						plpgsql_convert_ident(plpgsql_yytext, &name, 1);
						plpgsql_yyval.forvariable.name = name;
						plpgsql_yyval.forvariable.lineno  = plpgsql_scanner_lineno();
						plpgsql_yyval.forvariable.rec = plpgsql_yylval.rec;
						plpgsql_yyval.forvariable.row = NULL;
					}
    break;

  case 93:
#line 1036 "gram.y"
    {
						char		*name;

						plpgsql_convert_ident(plpgsql_yytext, &name, 1);
						plpgsql_yyval.forvariable.name = name;
						plpgsql_yyval.forvariable.lineno  = plpgsql_scanner_lineno();
						plpgsql_yyval.forvariable.row = plpgsql_yylval.row;
						plpgsql_yyval.forvariable.rec = NULL;
					}
    break;

  case 94:
#line 1048 "gram.y"
    {
						plpgsql_yyval.stmt = make_select_stmt();
						plpgsql_yyval.stmt->lineno = plpgsql_yyvsp[0].ival;
					}
    break;

  case 95:
#line 1055 "gram.y"
    {
						PLpgSQL_stmt_exit *new;

						new = palloc0(sizeof(PLpgSQL_stmt_exit));
						new->cmd_type = PLPGSQL_STMT_EXIT;
						new->is_exit  = plpgsql_yyvsp[-3].boolean;
						new->lineno	  = plpgsql_yyvsp[-2].ival;
						new->label	  = plpgsql_yyvsp[-1].str;
						new->cond	  = plpgsql_yyvsp[0].expr;

						plpgsql_yyval.stmt = (PLpgSQL_stmt *)new;
					}
    break;

  case 96:
#line 1070 "gram.y"
    {
						plpgsql_yyval.boolean = true;
					}
    break;

  case 97:
#line 1074 "gram.y"
    {
						plpgsql_yyval.boolean = false;
					}
    break;

  case 98:
#line 1080 "gram.y"
    {
						PLpgSQL_stmt_return *new;

						new = palloc0(sizeof(PLpgSQL_stmt_return));
						new->cmd_type = PLPGSQL_STMT_RETURN;
						new->lineno   = plpgsql_yyvsp[0].ival;
						new->expr	  = NULL;
						new->retvarno = -1;

						if (plpgsql_curr_compile->fn_retset)
						{
							if (plpgsql_yylex() != ';')
								plpgsql_yyerror("RETURN cannot have a parameter in function returning set; use RETURN NEXT");
						}
						else if (plpgsql_curr_compile->out_param_varno >= 0)
						{
							if (plpgsql_yylex() != ';')
								plpgsql_yyerror("RETURN cannot have a parameter in function with OUT parameters");
							new->retvarno = plpgsql_curr_compile->out_param_varno;
						}
						else if (plpgsql_curr_compile->fn_rettype == VOIDOID)
						{
							if (plpgsql_yylex() != ';')
								plpgsql_yyerror("RETURN cannot have a parameter in function returning void");
						}
						else if (plpgsql_curr_compile->fn_retistuple)
						{
							switch (plpgsql_yylex())
							{
								case K_NULL:
									/* we allow this to support RETURN NULL in triggers */
									break;

								case T_ROW:
									new->retvarno = plpgsql_yylval.row->rowno;
									break;

								case T_RECORD:
									new->retvarno = plpgsql_yylval.rec->recno;
									break;

								default:
									plpgsql_yyerror("RETURN must specify a record or row variable in function returning tuple");
									break;
							}
							if (plpgsql_yylex() != ';')
								plpgsql_yyerror("RETURN must specify a record or row variable in function returning tuple");
						}
						else
						{
							/*
							 * Note that a well-formed expression is
							 * _required_ here; anything else is a
							 * compile-time error.
							 */
							new->expr = plpgsql_read_expression(';', ";");
						}

						plpgsql_yyval.stmt = (PLpgSQL_stmt *)new;
					}
    break;

  case 99:
#line 1143 "gram.y"
    {
						PLpgSQL_stmt_return_next *new;

						if (!plpgsql_curr_compile->fn_retset)
							plpgsql_yyerror("cannot use RETURN NEXT in a non-SETOF function");

						new = palloc0(sizeof(PLpgSQL_stmt_return_next));
						new->cmd_type	= PLPGSQL_STMT_RETURN_NEXT;
						new->lineno		= plpgsql_yyvsp[0].ival;
						new->expr = NULL;
						new->retvarno	= -1;

						if (plpgsql_curr_compile->out_param_varno >= 0)
						{
							if (plpgsql_yylex() != ';')
								plpgsql_yyerror("RETURN NEXT cannot have a parameter in function with OUT parameters");
							new->retvarno = plpgsql_curr_compile->out_param_varno;
						}
						else if (plpgsql_curr_compile->fn_retistuple)
						{
							switch (plpgsql_yylex())
							{
								case T_ROW:
									new->retvarno = plpgsql_yylval.row->rowno;
									break;

								case T_RECORD:
									new->retvarno = plpgsql_yylval.rec->recno;
									break;

								default:
									plpgsql_yyerror("RETURN NEXT must specify a record or row variable in function returning tuple");
									break;
							}
							if (plpgsql_yylex() != ';')
								plpgsql_yyerror("RETURN NEXT must specify a record or row variable in function returning tuple");
						}
						else
							new->expr = plpgsql_read_expression(';', ";");

						plpgsql_yyval.stmt = (PLpgSQL_stmt *)new;
					}
    break;

  case 100:
#line 1188 "gram.y"
    {
						PLpgSQL_stmt_raise		*new;
						int	tok;

						new = palloc(sizeof(PLpgSQL_stmt_raise));

						new->cmd_type	= PLPGSQL_STMT_RAISE;
						new->lineno		= plpgsql_yyvsp[-2].ival;
						new->elog_level = plpgsql_yyvsp[-1].ival;
						new->message	= plpgsql_yyvsp[0].str;
						new->params		= NIL;

						tok = plpgsql_yylex();

						/*
						 * We expect either a semi-colon, which
						 * indicates no parameters, or a comma that
						 * begins the list of parameter expressions
						 */
						if (tok != ',' && tok != ';')
							plpgsql_yyerror("syntax error");

						if (tok == ',')
						{
							PLpgSQL_expr *expr;
							int term;

							for (;;)
							{
								expr = read_sql_construct(',', ';', ", or ;",
														  "SELECT ",
														  true, true, &term);
								new->params = lappend(new->params, expr);
								if (term == ';')
									break;
							}
						}

						plpgsql_yyval.stmt = (PLpgSQL_stmt *)new;
					}
    break;

  case 101:
#line 1231 "gram.y"
    {
						plpgsql_yyval.str = plpgsql_get_string_value();
					}
    break;

  case 102:
#line 1237 "gram.y"
    {
						plpgsql_yyval.ival = ERROR;
					}
    break;

  case 103:
#line 1241 "gram.y"
    {
						plpgsql_yyval.ival = WARNING;
					}
    break;

  case 104:
#line 1245 "gram.y"
    {
						plpgsql_yyval.ival = NOTICE;
					}
    break;

  case 105:
#line 1249 "gram.y"
    {
						plpgsql_yyval.ival = INFO;
					}
    break;

  case 106:
#line 1253 "gram.y"
    {
						plpgsql_yyval.ival = LOG;
					}
    break;

  case 107:
#line 1257 "gram.y"
    {
						plpgsql_yyval.ival = DEBUG1;
					}
    break;

  case 108:
#line 1263 "gram.y"
    {
						plpgsql_yyval.loop_body.stmts = plpgsql_yyvsp[-4].list;
						plpgsql_yyval.loop_body.end_label = plpgsql_yyvsp[-1].str;
					}
    break;

  case 109:
#line 1270 "gram.y"
    {
						PLpgSQL_stmt_execsql	*new;

						new = palloc(sizeof(PLpgSQL_stmt_execsql));
						new->cmd_type = PLPGSQL_STMT_EXECSQL;
						new->lineno   = plpgsql_yyvsp[0].ival;
						new->sqlstmt  = read_sql_stmt(plpgsql_yyvsp[-1].str);

						plpgsql_yyval.stmt = (PLpgSQL_stmt *)new;
					}
    break;

  case 110:
#line 1283 "gram.y"
    {
						PLpgSQL_stmt_dynexecute *new;
						PLpgSQL_expr *expr;
						int endtoken;

						expr = read_sql_construct(K_INTO, ';', "INTO|;", "SELECT ",
												  true, true, &endtoken);

						new = palloc(sizeof(PLpgSQL_stmt_dynexecute));
						new->cmd_type = PLPGSQL_STMT_DYNEXECUTE;
						new->lineno   = plpgsql_yyvsp[0].ival;
						new->query    = expr;
						new->rec = NULL;
						new->row = NULL;

						/*
						 * If we saw "INTO", look for a following row
						 * var, record var, or list of scalars.
						 */
						if (endtoken == K_INTO)
						{
							switch (plpgsql_yylex())
							{
								case T_ROW:
									check_assignable((PLpgSQL_datum *) plpgsql_yylval.row);
									new->row = plpgsql_yylval.row;
									break;

								case T_RECORD:
									check_assignable((PLpgSQL_datum *) plpgsql_yylval.row);
									new->rec = plpgsql_yylval.rec;
									break;

								case T_SCALAR:
									new->row = read_into_scalar_list(plpgsql_yytext, plpgsql_yylval.scalar);
									break;

								default:
									plpgsql_error_lineno = plpgsql_yyvsp[0].ival;
									ereport(ERROR,
											(errcode(ERRCODE_SYNTAX_ERROR),
											 errmsg("syntax error at \"%s\"", plpgsql_yytext),
											 errdetail("Expected record variable, row variable, "
													   "or list of scalar variables.")));
							}
							if (plpgsql_yylex() != ';')
								plpgsql_yyerror("syntax error");
						}

						plpgsql_yyval.stmt = (PLpgSQL_stmt *)new;
					}
    break;

  case 111:
#line 1338 "gram.y"
    {
						PLpgSQL_stmt_open *new;
						int				  tok;

						new = palloc0(sizeof(PLpgSQL_stmt_open));
						new->cmd_type = PLPGSQL_STMT_OPEN;
						new->lineno = plpgsql_yyvsp[-1].ival;
						new->curvar = plpgsql_yyvsp[0].var->varno;

						if (plpgsql_yyvsp[0].var->cursor_explicit_expr == NULL)
						{
						    tok = plpgsql_yylex();
							if (tok != K_FOR)
							{
								plpgsql_error_lineno = plpgsql_yyvsp[-1].ival;
								ereport(ERROR,
										(errcode(ERRCODE_SYNTAX_ERROR),
										 errmsg("syntax error at \"%s\"",
												plpgsql_yytext),
										 errdetail("Expected FOR to open a reference cursor.")));
							}

							tok = plpgsql_yylex();
							if (tok == K_EXECUTE)
							{
								new->dynquery = read_sql_stmt("SELECT ");
							}
							else
							{
								plpgsql_push_back_token(tok);
								new->query = read_sql_stmt("");
							}
						}
						else
						{
							if (plpgsql_yyvsp[0].var->cursor_explicit_argrow >= 0)
							{
								char   *cp;

								tok = plpgsql_yylex();
								if (tok != '(')
								{
									plpgsql_error_lineno = plpgsql_scanner_lineno();
									ereport(ERROR,
											(errcode(ERRCODE_SYNTAX_ERROR),
											 errmsg("cursor \"%s\" has arguments",
													plpgsql_yyvsp[0].var->refname)));
								}

								/*
								 * Push back the '(', else read_sql_stmt
								 * will complain about unbalanced parens.
								 */
								plpgsql_push_back_token(tok);

								new->argquery = read_sql_stmt("SELECT ");

								/*
								 * Now remove the leading and trailing parens,
								 * because we want "select 1, 2", not
								 * "select (1, 2)".
								 */
								cp = new->argquery->query;

								if (strncmp(cp, "SELECT", 6) != 0)
								{
									plpgsql_error_lineno = plpgsql_scanner_lineno();
									/* internal error */
									elog(ERROR, "expected \"SELECT (\", got \"%s\"",
										 new->argquery->query);
								}
								cp += 6;
								while (*cp == ' ') /* could be more than 1 space here */
									cp++;
								if (*cp != '(')
								{
									plpgsql_error_lineno = plpgsql_scanner_lineno();
									/* internal error */
									elog(ERROR, "expected \"SELECT (\", got \"%s\"",
										 new->argquery->query);
								}
								*cp = ' ';

								cp += strlen(cp) - 1;

								if (*cp != ')')
									plpgsql_yyerror("expected \")\"");
								*cp = '\0';
							}
							else
							{
								tok = plpgsql_yylex();
								if (tok == '(')
								{
									plpgsql_error_lineno = plpgsql_scanner_lineno();
									ereport(ERROR,
											(errcode(ERRCODE_SYNTAX_ERROR),
											 errmsg("cursor \"%s\" has no arguments",
													plpgsql_yyvsp[0].var->refname)));
								}

								if (tok != ';')
								{
									plpgsql_error_lineno = plpgsql_scanner_lineno();
									ereport(ERROR,
											(errcode(ERRCODE_SYNTAX_ERROR),
											 errmsg("syntax error at \"%s\"",
													plpgsql_yytext)));
								}
							}
						}

						plpgsql_yyval.stmt = (PLpgSQL_stmt *)new;
					}
    break;

  case 112:
#line 1455 "gram.y"
    {
						PLpgSQL_stmt_fetch *new;

						new = (PLpgSQL_stmt_fetch *)make_fetch_stmt();
						new->curvar = plpgsql_yyvsp[-1].ival;

						plpgsql_yyval.stmt = (PLpgSQL_stmt *)new;
						plpgsql_yyval.stmt->lineno = plpgsql_yyvsp[-2].ival;
					}
    break;

  case 113:
#line 1467 "gram.y"
    {
						PLpgSQL_stmt_close *new;

						new = palloc(sizeof(PLpgSQL_stmt_close));
						new->cmd_type = PLPGSQL_STMT_CLOSE;
						new->lineno = plpgsql_yyvsp[-2].ival;
						new->curvar = plpgsql_yyvsp[-1].ival;

						plpgsql_yyval.stmt = (PLpgSQL_stmt *)new;
					}
    break;

  case 114:
#line 1480 "gram.y"
    {
						/* We do not bother building a node for NULL */
						plpgsql_yyval.stmt = NULL;
					}
    break;

  case 115:
#line 1487 "gram.y"
    {
						if (plpgsql_yylval.scalar->dtype != PLPGSQL_DTYPE_VAR)
							plpgsql_yyerror("cursor variable must be a simple variable");

						if (((PLpgSQL_var *) plpgsql_yylval.scalar)->datatype->typoid != REFCURSOROID)
						{
							plpgsql_error_lineno = plpgsql_scanner_lineno();
							ereport(ERROR,
									(errcode(ERRCODE_DATATYPE_MISMATCH),
									 errmsg("\"%s\" must be of type cursor or refcursor",
											((PLpgSQL_var *) plpgsql_yylval.scalar)->refname)));
						}
						plpgsql_yyval.var = (PLpgSQL_var *) plpgsql_yylval.scalar;
					}
    break;

  case 116:
#line 1504 "gram.y"
    {
						if (plpgsql_yylval.scalar->dtype != PLPGSQL_DTYPE_VAR)
							plpgsql_yyerror("cursor variable must be a simple variable");

						if (((PLpgSQL_var *) plpgsql_yylval.scalar)->datatype->typoid != REFCURSOROID)
						{
							plpgsql_error_lineno = plpgsql_scanner_lineno();
							ereport(ERROR,
									(errcode(ERRCODE_DATATYPE_MISMATCH),
									 errmsg("\"%s\" must be of type refcursor",
											((PLpgSQL_var *) plpgsql_yylval.scalar)->refname)));
						}
						plpgsql_yyval.ival = plpgsql_yylval.scalar->dno;
					}
    break;

  case 117:
#line 1521 "gram.y"
    { plpgsql_yyval.str = pstrdup(plpgsql_yytext); }
    break;

  case 118:
#line 1523 "gram.y"
    { plpgsql_yyval.str = pstrdup(plpgsql_yytext); }
    break;

  case 119:
#line 1527 "gram.y"
    { plpgsql_yyval.exception_block = NULL; }
    break;

  case 120:
#line 1529 "gram.y"
    {
						/*
						 * We use a mid-rule action to add these
						 * special variables to the namespace before
						 * parsing the WHEN clauses themselves.
						 */
						PLpgSQL_exception_block *new = palloc(sizeof(PLpgSQL_exception_block));
						PLpgSQL_variable *var;

						var = plpgsql_build_variable("sqlstate", plpgsql_yyvsp[0].ival,
													 plpgsql_build_datatype(TEXTOID, -1),
													 true);
						((PLpgSQL_var *) var)->isconst = true;
						new->sqlstate_varno = var->dno;

						var = plpgsql_build_variable("sqlerrm", plpgsql_yyvsp[0].ival,
													 plpgsql_build_datatype(TEXTOID, -1),
													 true);
						((PLpgSQL_var *) var)->isconst = true;
						new->sqlerrm_varno = var->dno;

						plpgsql_yyval.exception_block = new;
					}
    break;

  case 121:
#line 1553 "gram.y"
    {
						PLpgSQL_exception_block *new = plpgsql_yyvsp[-1].exception_block;
						new->exc_list = plpgsql_yyvsp[0].list;

						plpgsql_yyval.exception_block = new;
					}
    break;

  case 122:
#line 1562 "gram.y"
    {
							plpgsql_yyval.list = lappend(plpgsql_yyvsp[-1].list, plpgsql_yyvsp[0].exception);
						}
    break;

  case 123:
#line 1566 "gram.y"
    {
							plpgsql_yyval.list = list_make1(plpgsql_yyvsp[0].exception);
						}
    break;

  case 124:
#line 1572 "gram.y"
    {
						PLpgSQL_exception *new;

						new = palloc0(sizeof(PLpgSQL_exception));
						new->lineno     = plpgsql_yyvsp[-3].ival;
						new->conditions = plpgsql_yyvsp[-2].condition;
						new->action	    = plpgsql_yyvsp[0].list;

						plpgsql_yyval.exception = new;
					}
    break;

  case 125:
#line 1585 "gram.y"
    {
							PLpgSQL_condition	*old;

							for (old = plpgsql_yyvsp[-2].condition; old->next != NULL; old = old->next)
								/* skip */ ;
							old->next = plpgsql_parse_err_condition(plpgsql_yyvsp[0].str);

							plpgsql_yyval.condition = plpgsql_yyvsp[-2].condition;
						}
    break;

  case 126:
#line 1595 "gram.y"
    {
							plpgsql_yyval.condition = plpgsql_parse_err_condition(plpgsql_yyvsp[0].str);
						}
    break;

  case 127:
#line 1601 "gram.y"
    { plpgsql_yyval.expr = plpgsql_read_expression(';', ";"); }
    break;

  case 128:
#line 1605 "gram.y"
    { plpgsql_yyval.expr = plpgsql_read_expression(']', "]"); }
    break;

  case 129:
#line 1609 "gram.y"
    { plpgsql_yyval.expr = plpgsql_read_expression(K_THEN, "THEN"); }
    break;

  case 130:
#line 1613 "gram.y"
    { plpgsql_yyval.expr = plpgsql_read_expression(K_LOOP, "LOOP"); }
    break;

  case 131:
#line 1617 "gram.y"
    {
						plpgsql_ns_push(NULL);
						plpgsql_yyval.str = NULL;
					}
    break;

  case 132:
#line 1622 "gram.y"
    {
						plpgsql_ns_push(plpgsql_yyvsp[-2].str);
						plpgsql_yyval.str = plpgsql_yyvsp[-2].str;
					}
    break;

  case 133:
#line 1629 "gram.y"
    {
						plpgsql_yyval.str = NULL;
					}
    break;

  case 134:
#line 1633 "gram.y"
    {
						char *label_name;
						plpgsql_convert_ident(plpgsql_yytext, &label_name, 1);
						plpgsql_yyval.str = label_name;
					}
    break;

  case 135:
#line 1639 "gram.y"
    {
						/* just to give a better error than "syntax error" */
						plpgsql_yyerror("no such label");
					}
    break;

  case 136:
#line 1646 "gram.y"
    { plpgsql_yyval.expr = NULL; }
    break;

  case 137:
#line 1648 "gram.y"
    { plpgsql_yyval.expr = plpgsql_yyvsp[0].expr; }
    break;

  case 138:
#line 1652 "gram.y"
    {
						char	*name;

						plpgsql_convert_ident(plpgsql_yytext, &name, 1);
						plpgsql_yyval.str = name;
					}
    break;

  case 139:
#line 1661 "gram.y"
    {
						plpgsql_yyval.ival = plpgsql_error_lineno = plpgsql_scanner_lineno();
					}
    break;


    }

/* Line 991 of yacc.c.  */
#line 3140 "y.tab.c"

  plpgsql_yyvsp -= plpgsql_yylen;
  plpgsql_yyssp -= plpgsql_yylen;


  PLPGSQL_YY_STACK_PRINT (plpgsql_yyss, plpgsql_yyssp);

  *++plpgsql_yyvsp = plpgsql_yyval;


  /* Now `shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */

  plpgsql_yyn = plpgsql_yyr1[plpgsql_yyn];

  plpgsql_yystate = plpgsql_yypgoto[plpgsql_yyn - PLPGSQL_YYNTOKENS] + *plpgsql_yyssp;
  if (0 <= plpgsql_yystate && plpgsql_yystate <= PLPGSQL_YYLAST && plpgsql_yycheck[plpgsql_yystate] == *plpgsql_yyssp)
    plpgsql_yystate = plpgsql_yytable[plpgsql_yystate];
  else
    plpgsql_yystate = plpgsql_yydefgoto[plpgsql_yyn - PLPGSQL_YYNTOKENS];

  goto plpgsql_yynewstate;


/*------------------------------------.
| plpgsql_yyerrlab -- here on detecting error |
`------------------------------------*/
plpgsql_yyerrlab:
  /* If not already recovering from an error, report this error.  */
  if (!plpgsql_yyerrstatus)
    {
      ++plpgsql_yynerrs;
#if PLPGSQL_YYERROR_VERBOSE
      plpgsql_yyn = plpgsql_yypact[plpgsql_yystate];

      if (PLPGSQL_YYPACT_NINF < plpgsql_yyn && plpgsql_yyn < PLPGSQL_YYLAST)
	{
	  PLPGSQL_YYSIZE_T plpgsql_yysize = 0;
	  int plpgsql_yytype = PLPGSQL_YYTRANSLATE (plpgsql_yychar);
	  char *plpgsql_yymsg;
	  int plpgsql_yyx, plpgsql_yycount;

	  plpgsql_yycount = 0;
	  /* Start PLPGSQL_YYX at -PLPGSQL_YYN if negative to avoid negative indexes in
	     PLPGSQL_YYCHECK.  */
	  for (plpgsql_yyx = plpgsql_yyn < 0 ? -plpgsql_yyn : 0;
	       plpgsql_yyx < (int) (sizeof (plpgsql_yytname) / sizeof (char *)); plpgsql_yyx++)
	    if (plpgsql_yycheck[plpgsql_yyx + plpgsql_yyn] == plpgsql_yyx && plpgsql_yyx != PLPGSQL_YYTERROR)
	      plpgsql_yysize += plpgsql_yystrlen (plpgsql_yytname[plpgsql_yyx]) + 15, plpgsql_yycount++;
	  plpgsql_yysize += plpgsql_yystrlen ("syntax error, unexpected ") + 1;
	  plpgsql_yysize += plpgsql_yystrlen (plpgsql_yytname[plpgsql_yytype]);
	  plpgsql_yymsg = (char *) PLPGSQL_YYSTACK_ALLOC (plpgsql_yysize);
	  if (plpgsql_yymsg != 0)
	    {
	      char *plpgsql_yyp = plpgsql_yystpcpy (plpgsql_yymsg, "syntax error, unexpected ");
	      plpgsql_yyp = plpgsql_yystpcpy (plpgsql_yyp, plpgsql_yytname[plpgsql_yytype]);

	      if (plpgsql_yycount < 5)
		{
		  plpgsql_yycount = 0;
		  for (plpgsql_yyx = plpgsql_yyn < 0 ? -plpgsql_yyn : 0;
		       plpgsql_yyx < (int) (sizeof (plpgsql_yytname) / sizeof (char *));
		       plpgsql_yyx++)
		    if (plpgsql_yycheck[plpgsql_yyx + plpgsql_yyn] == plpgsql_yyx && plpgsql_yyx != PLPGSQL_YYTERROR)
		      {
			const char *plpgsql_yyq = ! plpgsql_yycount ? ", expecting " : " or ";
			plpgsql_yyp = plpgsql_yystpcpy (plpgsql_yyp, plpgsql_yyq);
			plpgsql_yyp = plpgsql_yystpcpy (plpgsql_yyp, plpgsql_yytname[plpgsql_yyx]);
			plpgsql_yycount++;
		      }
		}
	      plpgsql_yyerror (plpgsql_yymsg);
	      PLPGSQL_YYSTACK_FREE (plpgsql_yymsg);
	    }
	  else
	    plpgsql_yyerror ("syntax error; also virtual memory exhausted");
	}
      else
#endif /* PLPGSQL_YYERROR_VERBOSE */
	plpgsql_yyerror ("syntax error");
    }



  if (plpgsql_yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
	 error, discard it.  */

      /* Return failure if at end of input.  */
      if (plpgsql_yychar == PLPGSQL_YYEOF)
        {
	  /* Pop the error token.  */
          PLPGSQL_YYPOPSTACK;
	  /* Pop the rest of the stack.  */
	  while (plpgsql_yyss < plpgsql_yyssp)
	    {
	      PLPGSQL_YYDSYMPRINTF ("Error: popping", plpgsql_yystos[*plpgsql_yyssp], plpgsql_yyvsp, plpgsql_yylsp);
	      plpgsql_yydestruct (plpgsql_yystos[*plpgsql_yyssp], plpgsql_yyvsp);
	      PLPGSQL_YYPOPSTACK;
	    }
	  PLPGSQL_YYABORT;
        }

      PLPGSQL_YYDSYMPRINTF ("Error: discarding", plpgsql_yytoken, &plpgsql_yylval, &plpgsql_yylloc);
      plpgsql_yydestruct (plpgsql_yytoken, &plpgsql_yylval);
      plpgsql_yychar = PLPGSQL_YYEMPTY;

    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto plpgsql_yyerrlab2;


/*----------------------------------------------------.
| plpgsql_yyerrlab1 -- error raised explicitly by an action.  |
`----------------------------------------------------*/
plpgsql_yyerrlab1:

  /* Suppress GCC warning that plpgsql_yyerrlab1 is unused when no action
     invokes PLPGSQL_YYERROR.  */
#if defined (__GNUC_MINOR__) && 2093 <= (__GNUC__ * 1000 + __GNUC_MINOR__)
  __attribute__ ((__unused__))
#endif


  goto plpgsql_yyerrlab2;


/*---------------------------------------------------------------.
| plpgsql_yyerrlab2 -- pop states until the error token can be shifted.  |
`---------------------------------------------------------------*/
plpgsql_yyerrlab2:
  plpgsql_yyerrstatus = 3;	/* Each real token shifted decrements this.  */

  for (;;)
    {
      plpgsql_yyn = plpgsql_yypact[plpgsql_yystate];
      if (plpgsql_yyn != PLPGSQL_YYPACT_NINF)
	{
	  plpgsql_yyn += PLPGSQL_YYTERROR;
	  if (0 <= plpgsql_yyn && plpgsql_yyn <= PLPGSQL_YYLAST && plpgsql_yycheck[plpgsql_yyn] == PLPGSQL_YYTERROR)
	    {
	      plpgsql_yyn = plpgsql_yytable[plpgsql_yyn];
	      if (0 < plpgsql_yyn)
		break;
	    }
	}

      /* Pop the current state because it cannot handle the error token.  */
      if (plpgsql_yyssp == plpgsql_yyss)
	PLPGSQL_YYABORT;

      PLPGSQL_YYDSYMPRINTF ("Error: popping", plpgsql_yystos[*plpgsql_yyssp], plpgsql_yyvsp, plpgsql_yylsp);
      plpgsql_yydestruct (plpgsql_yystos[plpgsql_yystate], plpgsql_yyvsp);
      plpgsql_yyvsp--;
      plpgsql_yystate = *--plpgsql_yyssp;

      PLPGSQL_YY_STACK_PRINT (plpgsql_yyss, plpgsql_yyssp);
    }

  if (plpgsql_yyn == PLPGSQL_YYFINAL)
    PLPGSQL_YYACCEPT;

  PLPGSQL_YYDPRINTF ((stderr, "Shifting error token, "));

  *++plpgsql_yyvsp = plpgsql_yylval;


  plpgsql_yystate = plpgsql_yyn;
  goto plpgsql_yynewstate;


/*-------------------------------------.
| plpgsql_yyacceptlab -- PLPGSQL_YYACCEPT comes here.  |
`-------------------------------------*/
plpgsql_yyacceptlab:
  plpgsql_yyresult = 0;
  goto plpgsql_yyreturn;

/*-----------------------------------.
| plpgsql_yyabortlab -- PLPGSQL_YYABORT comes here.  |
`-----------------------------------*/
plpgsql_yyabortlab:
  plpgsql_yyresult = 1;
  goto plpgsql_yyreturn;

#ifndef plpgsql_yyoverflow
/*----------------------------------------------.
| plpgsql_yyoverflowlab -- parser overflow comes here.  |
`----------------------------------------------*/
plpgsql_yyoverflowlab:
  plpgsql_yyerror ("parser stack overflow");
  plpgsql_yyresult = 2;
  /* Fall through.  */
#endif

plpgsql_yyreturn:
#ifndef plpgsql_yyoverflow
  if (plpgsql_yyss != plpgsql_yyssa)
    PLPGSQL_YYSTACK_FREE (plpgsql_yyss);
#endif
  return plpgsql_yyresult;
}


#line 1666 "gram.y"



#define MAX_EXPR_PARAMS  1024

/*
 * determine the expression parameter position to use for a plpgsql datum
 *
 * It is important that any given plpgsql datum map to just one parameter.
 * We used to be sloppy and assign a separate parameter for each occurrence
 * of a datum reference, but that fails for situations such as "select DATUM
 * from ... group by DATUM".
 *
 * The params[] array must be of size MAX_EXPR_PARAMS.
 */
static int
assign_expr_param(int dno, int *params, int *nparams)
{
	int		i;

	/* already have an instance of this dno? */
	for (i = 0; i < *nparams; i++)
	{
		if (params[i] == dno)
			return i+1;
	}
	/* check for array overflow */
	if (*nparams >= MAX_EXPR_PARAMS)
	{
		plpgsql_error_lineno = plpgsql_scanner_lineno();
		ereport(ERROR,
				(errcode(ERRCODE_PROGRAM_LIMIT_EXCEEDED),
				 errmsg("too many variables specified in SQL statement")));
	}
	/* add new parameter dno to array */
	params[*nparams] = dno;
	(*nparams)++;
	return *nparams;
}


PLpgSQL_expr *
plpgsql_read_expression(int until, const char *expected)
{
	return read_sql_construct(until, 0, expected, "SELECT ", true, true, NULL);
}

static PLpgSQL_expr *
read_sql_stmt(const char *sqlstart)
{
	return read_sql_construct(';', 0, ";", sqlstart, false, true, NULL);
}

/*
 * Read a SQL construct and build a PLpgSQL_expr for it.
 *
 * until:		token code for expected terminator
 * until2:		token code for alternate terminator (pass 0 if none)
 * expected:	text to use in complaining that terminator was not found
 * sqlstart:	text to prefix to the accumulated SQL text
 * isexpression: whether to say we're reading an "expression" or a "statement"
 * valid_sql:   whether to check the syntax of the expr (prefixed with sqlstart)
 * endtoken:	if not NULL, ending token is stored at *endtoken
 *				(this is only interesting if until2 isn't zero)
 */
static PLpgSQL_expr *
read_sql_construct(int until,
				   int until2,
				   const char *expected,
				   const char *sqlstart,
				   bool isexpression,
				   bool valid_sql,
				   int *endtoken)
{
	int					tok;
	int					lno;
	PLpgSQL_dstring		ds;
	int					parenlevel = 0;
	int					nparams = 0;
	int					params[MAX_EXPR_PARAMS];
	char				buf[32];
	PLpgSQL_expr		*expr;

	lno = plpgsql_scanner_lineno();
	plpgsql_dstring_init(&ds);
	plpgsql_dstring_append(&ds, sqlstart);

	for (;;)
	{
		tok = plpgsql_yylex();
		if (tok == until && parenlevel == 0)
			break;
		if (tok == until2 && parenlevel == 0)
			break;
		if (tok == '(' || tok == '[')
			parenlevel++;
		else if (tok == ')' || tok == ']')
		{
			parenlevel--;
			if (parenlevel < 0)
				ereport(ERROR,
						(errcode(ERRCODE_SYNTAX_ERROR),
						 errmsg("mismatched parentheses")));
		}
		/*
		 * End of function definition is an error, and we don't expect to
		 * hit a semicolon either (unless it's the until symbol, in which
		 * case we should have fallen out above).
		 */
		if (tok == 0 || tok == ';')
		{
			plpgsql_error_lineno = lno;
			if (parenlevel != 0)
				ereport(ERROR,
						(errcode(ERRCODE_SYNTAX_ERROR),
						 errmsg("mismatched parentheses")));
			if (isexpression)
				ereport(ERROR,
						(errcode(ERRCODE_SYNTAX_ERROR),
						 errmsg("missing \"%s\" at end of SQL expression",
								expected)));
			else
				ereport(ERROR,
						(errcode(ERRCODE_SYNTAX_ERROR),
						 errmsg("missing \"%s\" at end of SQL statement",
								expected)));
		}

		if (plpgsql_SpaceScanned)
			plpgsql_dstring_append(&ds, " ");

		switch (tok)
		{
			case T_SCALAR:
				snprintf(buf, sizeof(buf), " $%d ",
						 assign_expr_param(plpgsql_yylval.scalar->dno,
										   params, &nparams));
				plpgsql_dstring_append(&ds, buf);
				break;

			case T_ROW:
				snprintf(buf, sizeof(buf), " $%d ",
						 assign_expr_param(plpgsql_yylval.row->rowno,
										   params, &nparams));
				plpgsql_dstring_append(&ds, buf);
				break;

			case T_RECORD:
				snprintf(buf, sizeof(buf), " $%d ",
						 assign_expr_param(plpgsql_yylval.rec->recno,
										   params, &nparams));
				plpgsql_dstring_append(&ds, buf);
				break;

			default:
				plpgsql_dstring_append(&ds, plpgsql_yytext);
				break;
		}
	}

	if (endtoken)
		*endtoken = tok;

	expr = palloc(sizeof(PLpgSQL_expr) + sizeof(int) * nparams - sizeof(int));
	expr->dtype			= PLPGSQL_DTYPE_EXPR;
	expr->query			= pstrdup(plpgsql_dstring_get(&ds));
	expr->plan			= NULL;
	expr->nparams		= nparams;
	while(nparams-- > 0)
		expr->params[nparams] = params[nparams];
	plpgsql_dstring_free(&ds);

	if (valid_sql)
		check_sql_expr(expr->query);

	return expr;
}

static PLpgSQL_type *
read_datatype(int tok)
{
	int					lno;
	PLpgSQL_dstring		ds;
	PLpgSQL_type		*result;
	bool				needspace = false;
	int					parenlevel = 0;

	lno = plpgsql_scanner_lineno();

	/* Often there will be a lookahead token, but if not, get one */
	if (tok == PLPGSQL_YYEMPTY)
		tok = plpgsql_yylex();

	if (tok == T_DTYPE)
	{
		/* lexer found word%TYPE and did its thing already */
		return plpgsql_yylval.dtype;
	}

	plpgsql_dstring_init(&ds);

	while (tok != ';')
	{
		if (tok == 0)
		{
			plpgsql_error_lineno = lno;
			if (parenlevel != 0)
				ereport(ERROR,
						(errcode(ERRCODE_SYNTAX_ERROR),
						 errmsg("mismatched parentheses")));
			ereport(ERROR,
					(errcode(ERRCODE_SYNTAX_ERROR),
					 errmsg("incomplete datatype declaration")));
		}
		/* Possible followers for datatype in a declaration */
		if (tok == K_NOT || tok == K_ASSIGN || tok == K_DEFAULT)
			break;
		/* Possible followers for datatype in a cursor_arg list */
		if ((tok == ',' || tok == ')') && parenlevel == 0)
			break;
		if (tok == '(')
			parenlevel++;
		else if (tok == ')')
			parenlevel--;
		if (needspace)
			plpgsql_dstring_append(&ds, " ");
		needspace = true;
		plpgsql_dstring_append(&ds, plpgsql_yytext);

		tok = plpgsql_yylex();
	}

	plpgsql_push_back_token(tok);

	plpgsql_error_lineno = lno;	/* in case of error in parse_datatype */

	result = plpgsql_parse_datatype(plpgsql_dstring_get(&ds));

	plpgsql_dstring_free(&ds);

	return result;
}

static PLpgSQL_stmt *
make_select_stmt(void)
{
	PLpgSQL_dstring		ds;
	int					nparams = 0;
	int					params[MAX_EXPR_PARAMS];
	char				buf[32];
	PLpgSQL_expr		*expr;
	PLpgSQL_row			*row = NULL;
	PLpgSQL_rec			*rec = NULL;
	int					tok;
	bool				have_into = false;

	plpgsql_dstring_init(&ds);
	plpgsql_dstring_append(&ds, "SELECT ");

	while (1)
	{
		tok = plpgsql_yylex();

		if (tok == ';')
			break;
		if (tok == 0)
		{
			plpgsql_error_lineno = plpgsql_scanner_lineno();
			ereport(ERROR,
					(errcode(ERRCODE_SYNTAX_ERROR),
					 errmsg("unexpected end of function definition")));
		}
		if (tok == K_INTO)
		{
			if (have_into)
			{
				plpgsql_error_lineno = plpgsql_scanner_lineno();
				ereport(ERROR,
						(errcode(ERRCODE_SYNTAX_ERROR),
						 errmsg("INTO specified more than once")));
			}
			tok = plpgsql_yylex();
			switch (tok)
			{
				case T_ROW:
					row = plpgsql_yylval.row;
					have_into = true;
					break;

				case T_RECORD:
					rec = plpgsql_yylval.rec;
					have_into = true;
					break;

				case T_SCALAR:
					row = read_into_scalar_list(plpgsql_yytext, plpgsql_yylval.scalar);
					have_into = true;
					break;

				default:
					/* Treat the INTO as non-special */
					plpgsql_dstring_append(&ds, " INTO ");
					plpgsql_push_back_token(tok);
					break;
			}
			continue;
		}

		if (plpgsql_SpaceScanned)
			plpgsql_dstring_append(&ds, " ");

		switch (tok)
		{
			case T_SCALAR:
				snprintf(buf, sizeof(buf), " $%d ",
						 assign_expr_param(plpgsql_yylval.scalar->dno,
										   params, &nparams));
				plpgsql_dstring_append(&ds, buf);
				break;

			case T_ROW:
				snprintf(buf, sizeof(buf), " $%d ",
						 assign_expr_param(plpgsql_yylval.row->rowno,
										   params, &nparams));
				plpgsql_dstring_append(&ds, buf);
				break;

			case T_RECORD:
				snprintf(buf, sizeof(buf), " $%d ",
						 assign_expr_param(plpgsql_yylval.rec->recno,
										   params, &nparams));
				plpgsql_dstring_append(&ds, buf);
				break;

			default:
				plpgsql_dstring_append(&ds, plpgsql_yytext);
				break;
		}
	}

	expr = palloc(sizeof(PLpgSQL_expr) + sizeof(int) * nparams - sizeof(int));
	expr->dtype			= PLPGSQL_DTYPE_EXPR;
	expr->query			= pstrdup(plpgsql_dstring_get(&ds));
	expr->plan			= NULL;
	expr->nparams		= nparams;
	while(nparams-- > 0)
		expr->params[nparams] = params[nparams];
	plpgsql_dstring_free(&ds);

	check_sql_expr(expr->query);

	if (have_into)
	{
		PLpgSQL_stmt_select *select;

		select = palloc0(sizeof(PLpgSQL_stmt_select));
		select->cmd_type = PLPGSQL_STMT_SELECT;
		select->rec		 = rec;
		select->row		 = row;
		select->query	 = expr;

		return (PLpgSQL_stmt *)select;
	}
	else
	{
		PLpgSQL_stmt_execsql *execsql;

		execsql = palloc(sizeof(PLpgSQL_stmt_execsql));
		execsql->cmd_type = PLPGSQL_STMT_EXECSQL;
		execsql->sqlstmt  = expr;

		return (PLpgSQL_stmt *)execsql;
	}
}


static PLpgSQL_stmt *
make_fetch_stmt(void)
{
	int					tok;
	PLpgSQL_row		   *row = NULL;
	PLpgSQL_rec		   *rec = NULL;
	PLpgSQL_stmt_fetch *fetch;

	/* We have already parsed everything through the INTO keyword */

	tok = plpgsql_yylex();
	switch (tok)
	{
		case T_ROW:
			row = plpgsql_yylval.row;
			break;

		case T_RECORD:
			rec = plpgsql_yylval.rec;
			break;

		case T_SCALAR:
			row = read_into_scalar_list(plpgsql_yytext, plpgsql_yylval.scalar);
			break;

		default:
			plpgsql_yyerror("syntax error");
	}

	tok = plpgsql_yylex();
	if (tok != ';')
		plpgsql_yyerror("syntax error");

	fetch = palloc0(sizeof(PLpgSQL_stmt_select));
	fetch->cmd_type = PLPGSQL_STMT_FETCH;
	fetch->rec		 = rec;
	fetch->row		 = row;

	return (PLpgSQL_stmt *)fetch;
}


static void
check_assignable(PLpgSQL_datum *datum)
{
	switch (datum->dtype)
	{
		case PLPGSQL_DTYPE_VAR:
			if (((PLpgSQL_var *) datum)->isconst)
			{
				plpgsql_error_lineno = plpgsql_scanner_lineno();
				ereport(ERROR,
						(errcode(ERRCODE_ERROR_IN_ASSIGNMENT),
						 errmsg("\"%s\" is declared CONSTANT",
								((PLpgSQL_var *) datum)->refname)));
			}
			break;
		case PLPGSQL_DTYPE_ROW:
			/* always assignable? */
			break;
		case PLPGSQL_DTYPE_REC:
			/* always assignable?  What about NEW/OLD? */
			break;
		case PLPGSQL_DTYPE_RECFIELD:
			/* always assignable? */
			break;
		case PLPGSQL_DTYPE_ARRAYELEM:
			/* always assignable? */
			break;
		case PLPGSQL_DTYPE_TRIGARG:
			plpgsql_yyerror("cannot assign to tg_argv");
			break;
		default:
			elog(ERROR, "unrecognized dtype: %d", datum->dtype);
			break;
	}
}

/*
 * Given the first datum and name in the INTO list, continue to read
 * comma-separated scalar variables until we run out. Then construct
 * and return a fake "row" variable that represents the list of
 * scalars.
 */
static PLpgSQL_row *
read_into_scalar_list(const char *initial_name,
					  PLpgSQL_datum *initial_datum)
{
	int				 nfields;
	char			*fieldnames[1024];
	int				 varnos[1024];
	PLpgSQL_row		*row;
	int				 tok;

	check_assignable(initial_datum);
	fieldnames[0] = pstrdup(initial_name);
	varnos[0]	  = initial_datum->dno;
	nfields		  = 1;

	while ((tok = plpgsql_yylex()) == ',')
	{
		/* Check for array overflow */
		if (nfields >= 1024)
		{
			plpgsql_error_lineno = plpgsql_scanner_lineno();
			ereport(ERROR,
					(errcode(ERRCODE_PROGRAM_LIMIT_EXCEEDED),
					 errmsg("too many INTO variables specified")));
		}

		tok = plpgsql_yylex();
		switch(tok)
		{
			case T_SCALAR:
				check_assignable(plpgsql_yylval.scalar);
				fieldnames[nfields] = pstrdup(plpgsql_yytext);
				varnos[nfields++]	= plpgsql_yylval.scalar->dno;
				break;

			default:
				plpgsql_error_lineno = plpgsql_scanner_lineno();
				ereport(ERROR,
						(errcode(ERRCODE_SYNTAX_ERROR),
						 errmsg("\"%s\" is not a variable",
								plpgsql_yytext)));
		}
	}

	/*
	 * We read an extra, non-comma character from plpgsql_yylex(), so push it
	 * back onto the input stream
	 */
	plpgsql_push_back_token(tok);

	row = palloc(sizeof(PLpgSQL_row));
	row->dtype = PLPGSQL_DTYPE_ROW;
	row->refname = pstrdup("*internal*");
	row->lineno = plpgsql_scanner_lineno();
	row->rowtupdesc = NULL;
	row->nfields = nfields;
	row->fieldnames = palloc(sizeof(char *) * nfields);
	row->varnos = palloc(sizeof(int) * nfields);
	while (--nfields >= 0)
	{
		row->fieldnames[nfields] = fieldnames[nfields];
		row->varnos[nfields] = varnos[nfields];
	}

	plpgsql_adddatum((PLpgSQL_datum *)row);

	return row;
}

/*
 * When the PL/PgSQL parser expects to see a SQL statement, it is very
 * liberal in what it accepts; for example, we often assume an
 * unrecognized keyword is the beginning of a SQL statement. This
 * avoids the need to duplicate parts of the SQL grammar in the
 * PL/PgSQL grammar, but it means we can accept wildly malformed
 * input. To try and catch some of the more obviously invalid input,
 * we run the strings we expect to be SQL statements through the main
 * SQL parser.
 *
 * We only invoke the raw parser (not the analyzer); this doesn't do
 * any database access and does not check any semantic rules, it just
 * checks for basic syntactic correctness. We do this here, rather
 * than after parsing has finished, because a malformed SQL statement
 * may cause the PL/PgSQL parser to become confused about statement
 * borders. So it is best to bail out as early as we can.
 */
static void
check_sql_expr(const char *stmt)
{
	ErrorContextCallback  syntax_errcontext;
	ErrorContextCallback *previous_errcontext;
	MemoryContext oldCxt;

	if (!plpgsql_check_syntax)
		return;

	/*
	 * Setup error traceback support for ereport(). The previous
	 * ereport callback is installed by pl_comp.c, but we don't want
	 * that to be invoked (since it will try to transpose the syntax
	 * error to be relative to the CREATE FUNCTION), so temporarily
	 * remove it from the list of callbacks.
	 */
	Assert(error_context_stack->callback == plpgsql_compile_error_callback);

	previous_errcontext = error_context_stack;
	syntax_errcontext.callback = plpgsql_sql_error_callback;
	syntax_errcontext.arg = (char *) stmt;
	syntax_errcontext.previous = error_context_stack->previous;
	error_context_stack = &syntax_errcontext;

	oldCxt = MemoryContextSwitchTo(compile_tmp_cxt);
	(void) raw_parser(stmt);
	MemoryContextSwitchTo(oldCxt);

	/* Restore former ereport callback */
	error_context_stack = previous_errcontext;
}

static void
plpgsql_sql_error_callback(void *arg)
{
	char *sql_stmt = (char *) arg;

	Assert(plpgsql_error_funcname);

	errcontext("SQL statement in PL/PgSQL function \"%s\" near line %d",
			   plpgsql_error_funcname, plpgsql_error_lineno);
	internalerrquery(sql_stmt);
	internalerrposition(geterrposition());
	errposition(0);
}

static void
check_labels(const char *start_label, const char *end_label)
{
	if (end_label)
	{
		if (!start_label)
		{
			plpgsql_error_lineno = plpgsql_scanner_lineno();
			ereport(ERROR,
					(errcode(ERRCODE_SYNTAX_ERROR),
					 errmsg("end label \"%s\" specified for unlabelled block",
							end_label)));
		}

		if (strcmp(start_label, end_label) != 0)
		{
			plpgsql_error_lineno = plpgsql_scanner_lineno();
			ereport(ERROR,
					(errcode(ERRCODE_SYNTAX_ERROR),
					 errmsg("end label \"%s\" differs from block's label \"%s\"",
							end_label, start_label)));
		}
	}
}

#include "pl_scan.c"

