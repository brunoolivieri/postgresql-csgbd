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

/* All symbols defined below should begin with Int_yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 0

/* Using locations.  */
#define YYLSP_NEEDED 0



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




/* Copy the first part of user declarations.  */
#line 1 "bootparse.y"

/*-------------------------------------------------------------------------
 *
 * bootparse.y
 *	  yacc parser grammar for the "backend" initialization program.
 *
 * Portions Copyright (c) 1996-2005, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  $PostgreSQL: pgsql/src/backend/bootstrap/bootparse.y,v 1.78 2005/08/26 03:07:00 tgl Exp $
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include <unistd.h>

#include "access/attnum.h"
#include "access/htup.h"
#include "access/itup.h"
#include "access/skey.h"
#include "access/tupdesc.h"
#include "access/xact.h"
#include "bootstrap/bootstrap.h"
#include "catalog/catalog.h"
#include "catalog/heap.h"
#include "catalog/pg_am.h"
#include "catalog/pg_attribute.h"
#include "catalog/pg_authid.h"
#include "catalog/pg_class.h"
#include "catalog/pg_namespace.h"
#include "catalog/pg_tablespace.h"
#include "commands/defrem.h"
#include "miscadmin.h"
#include "nodes/makefuncs.h"
#include "nodes/nodes.h"
#include "nodes/parsenodes.h"
#include "nodes/pg_list.h"
#include "nodes/primnodes.h"
#include "rewrite/prs2lock.h"
#include "storage/block.h"
#include "storage/fd.h"
#include "storage/ipc.h"
#include "storage/itemptr.h"
#include "storage/off.h"
#include "storage/smgr.h"
#include "tcop/dest.h"
#include "utils/rel.h"

#define atooid(x)	((Oid) strtoul((x), NULL, 10))


static void
do_start(void)
{
	StartTransactionCommand();
	elog(DEBUG4, "start transaction");
}


static void
do_end(void)
{
	CommitTransactionCommand();
	elog(DEBUG4, "commit transaction");
	CHECK_FOR_INTERRUPTS();		/* allow SIGINT to kill bootstrap run */
	if (isatty(0))
	{
		printf("bootstrap> ");
		fflush(stdout);
	}
}


int num_columns_read = 0;



/* Enabling traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 0
#endif

#if ! defined (YYSTYPE) && ! defined (YYSTYPE_IS_DECLARED)
#line 83 "bootparse.y"
typedef union YYSTYPE {
	List		*list;
	IndexElem	*ielem;
	char		*str;
	int			ival;
	Oid			oidval;
} YYSTYPE;
/* Line 191 of yacc.c.  */
#line 216 "y.tab.c"
# define Int_yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
# define YYSTYPE_IS_TRIVIAL 1
#endif



/* Copy the second part of user declarations.  */


/* Line 214 of yacc.c.  */
#line 228 "y.tab.c"

#if ! defined (Int_yyoverflow) || YYERROR_VERBOSE

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# if YYSTACK_USE_ALLOCA
#  define YYSTACK_ALLOC alloca
# else
#  ifndef YYSTACK_USE_ALLOCA
#   if defined (alloca) || defined (_ALLOCA_H)
#    define YYSTACK_ALLOC alloca
#   else
#    ifdef __GNUC__
#     define YYSTACK_ALLOC __builtin_alloca
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's `empty if-body' warning. */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (0)
# else
#  if defined (__STDC__) || defined (__cplusplus)
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   define YYSIZE_T size_t
#  endif
#  define YYSTACK_ALLOC malloc
#  define YYSTACK_FREE free
# endif
#endif /* ! defined (Int_yyoverflow) || YYERROR_VERBOSE */


#if (! defined (Int_yyoverflow) \
     && (! defined (__cplusplus) \
	 || (YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union Int_yyalloc
{
  short Int_yyss;
  YYSTYPE Int_yyvs;
  };

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (sizeof (union Int_yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (short) + sizeof (YYSTYPE))				\
      + YYSTACK_GAP_MAXIMUM)

/* Copy COUNT objects from FROM to TO.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if 1 < __GNUC__
#   define YYCOPY(To, From, Count) \
      __builtin_memcpy (To, From, (Count) * sizeof (*(From)))
#  else
#   define YYCOPY(To, From, Count)		\
      do					\
	{					\
	  register YYSIZE_T Int_yyi;		\
	  for (Int_yyi = 0; Int_yyi < (Count); Int_yyi++)	\
	    (To)[Int_yyi] = (From)[Int_yyi];		\
	}					\
      while (0)
#  endif
# endif

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack)					\
    do									\
      {									\
	YYSIZE_T Int_yynewbytes;						\
	YYCOPY (&Int_yyptr->Stack, Stack, Int_yysize);				\
	Stack = &Int_yyptr->Stack;						\
	Int_yynewbytes = Int_yystacksize * sizeof (*Stack) + YYSTACK_GAP_MAXIMUM; \
	Int_yyptr += Int_yynewbytes / sizeof (*Int_yyptr);				\
      }									\
    while (0)

#endif

#if defined (__STDC__) || defined (__cplusplus)
   typedef signed char Int_yysigned_char;
#else
   typedef short Int_yysigned_char;
#endif

/* YYFINAL -- State number of the termination state. */
#define YYFINAL  27
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   78

/* YYNTOKENS -- Number of terminals. */
#define YYNTOKENS  27
/* YYNNTS -- Number of nonterminals. */
#define YYNNTS  27
/* YYNRULES -- Number of rules. */
#define YYNRULES  46
/* YYNRULES -- Number of states. */
#define YYNSTATES  85

/* YYTRANSLATE(YYLEX) -- Bison symbol number corresponding to YYLEX.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   281

#define YYTRANSLATE(YYX) 						\
  ((unsigned int) (YYX) <= YYMAXUTOK ? Int_yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[YYLEX] -- Bison symbol number corresponding to YYLEX.  */
static const unsigned char Int_yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
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
      25,    26
};

#if YYDEBUG
/* YYPRHS[YYN] -- Index of the first RHS symbol of rule number YYN in
   YYRHS.  */
static const unsigned char Int_yyprhs[] =
{
       0,     0,     3,     5,     6,     8,    11,    13,    15,    17,
      19,    21,    23,    25,    28,    31,    33,    34,    35,    47,
      48,    55,    67,    80,    83,    87,    89,    92,    94,    95,
      97,    98,   100,   101,   103,   107,   111,   113,   117,   118,
     120,   123,   127,   129,   131,   133,   135
};

/* YYRHS -- A `-1'-separated list of the rules' RHS. */
static const Int_yysigned_char Int_yyrhs[] =
{
      28,     0,    -1,    29,    -1,    -1,    30,    -1,    29,    30,
      -1,    31,    -1,    32,    -1,    33,    -1,    36,    -1,    38,
      -1,    39,    -1,    40,    -1,     5,    53,    -1,     6,    53,
      -1,     6,    -1,    -1,    -1,     7,    43,    44,    45,    53,
      48,    18,    34,    46,    35,    19,    -1,    -1,     8,    49,
      37,    18,    50,    19,    -1,     9,    10,    53,    48,    11,
      53,    12,    53,    18,    41,    19,    -1,     9,    15,    10,
      53,    48,    11,    53,    12,    53,    18,    41,    19,    -1,
      13,    14,    -1,    41,    16,    42,    -1,    42,    -1,    53,
      53,    -1,    21,    -1,    -1,    22,    -1,    -1,    23,    -1,
      -1,    47,    -1,    46,    16,    47,    -1,    53,    17,    53,
      -1,    53,    -1,    20,    17,    48,    -1,    -1,    51,    -1,
      50,    51,    -1,    50,    16,    51,    -1,    53,    -1,    52,
      -1,    24,    -1,     3,    -1,     4,    -1
};

/* YYRLINE[YYN] -- source line where rule number YYN was defined.  */
static const unsigned short Int_yyrline[] =
{
       0,   111,   111,   112,   116,   117,   121,   122,   123,   124,
     125,   126,   127,   131,   140,   146,   156,   166,   155,   219,
     218,   243,   261,   279,   289,   290,   294,   305,   306,   310,
     311,   315,   316,   320,   321,   325,   334,   338,   339,   343,
     344,   345,   349,   351,   353,   358,   362
};
#endif

#if YYDEBUG || YYERROR_VERBOSE
/* YYTNME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals. */
static const char *const Int_yytname[] =
{
  "$end", "error", "$undefined", "CONST_P", "ID", "OPEN", "XCLOSE", 
  "XCREATE", "INSERT_TUPLE", "XDECLARE", "INDEX", "ON", "USING", "XBUILD", 
  "INDICES", "UNIQUE", "COMMA", "EQUALS", "LPAREN", "RPAREN", "OBJ_ID", 
  "XBOOTSTRAP", "XSHARED_RELATION", "XWITHOUT_OIDS", "NULLVAL", "low", 
  "high", "$accept", "TopLevel", "Boot_Queries", "Boot_Query", 
  "Boot_OpenStmt", "Boot_CloseStmt", "Boot_CreateStmt", "@1", "@2", 
  "Boot_InsertStmt", "@3", "Boot_DeclareIndexStmt", 
  "Boot_DeclareUniqueIndexStmt", "Boot_BuildIndsStmt", 
  "boot_index_params", "boot_index_param", "optbootstrap", 
  "optsharedrelation", "optwithoutoids", "boot_typelist", 
  "boot_type_thing", "oidspec", "optoideq", "boot_tuplelist", 
  "boot_tuple", "boot_const", "boot_ident", 0
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[YYLEX-NUM] -- Internal token number corresponding to
   token YYLEX-NUM.  */
static const unsigned short Int_yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281
};
# endif

/* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const unsigned char Int_yyr1[] =
{
       0,    27,    28,    28,    29,    29,    30,    30,    30,    30,
      30,    30,    30,    31,    32,    32,    34,    35,    33,    37,
      36,    38,    39,    40,    41,    41,    42,    43,    43,    44,
      44,    45,    45,    46,    46,    47,    48,    49,    49,    50,
      50,    50,    51,    51,    51,    52,    53
};

/* YYR2[YYN] -- Number of symbols composing right hand side of rule YYN.  */
static const unsigned char Int_yyr2[] =
{
       0,     2,     1,     0,     1,     2,     1,     1,     1,     1,
       1,     1,     1,     2,     2,     1,     0,     0,    11,     0,
       6,    11,    12,     2,     3,     1,     2,     1,     0,     1,
       0,     1,     0,     1,     3,     3,     1,     3,     0,     1,
       2,     3,     1,     1,     1,     1,     1
};

/* YYDEFACT[STATE-NAME] -- Default rule to reduce with in state
   STATE-NUM when YYTABLE doesn't specify something else to do.  Zero
   means the default is an error.  */
static const unsigned char Int_yydefact[] =
{
       3,     0,    15,    28,    38,     0,     0,     0,     2,     4,
       6,     7,     8,     9,    10,    11,    12,    46,    13,    14,
      27,    30,     0,    19,     0,     0,    23,     1,     5,    29,
      32,     0,     0,     0,     0,    31,     0,    37,    36,     0,
       0,     0,     0,    45,    44,     0,    39,    43,    42,     0,
       0,     0,     0,    20,    40,     0,     0,    16,    41,     0,
       0,     0,     0,     0,    17,    33,     0,     0,     0,     0,
       0,     0,     0,    25,     0,     0,    34,    18,    35,     0,
      21,    26,     0,    24,    22
};

/* YYDEFGOTO[NTERM-NUM]. */
static const Int_yysigned_char Int_yydefgoto[] =
{
      -1,     7,     8,     9,    10,    11,    12,    61,    70,    13,
      32,    14,    15,    16,    72,    73,    21,    30,    36,    64,
      65,    37,    23,    45,    46,    47,    38
};

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
#define YYPACT_NINF -39
static const Int_yysigned_char Int_yypact[] =
{
      23,    11,    11,    -3,     5,    -2,     7,    22,    23,   -39,
     -39,   -39,   -39,   -39,   -39,   -39,   -39,   -39,   -39,   -39,
     -39,    12,    10,   -39,    11,    27,   -39,   -39,   -39,   -39,
      16,    11,    24,    11,    11,   -39,    11,   -39,   -39,     2,
      29,    11,    11,   -39,   -39,     0,   -39,   -39,   -39,    11,
      30,    25,     2,   -39,   -39,    33,    11,   -39,   -39,    11,
      34,    11,    31,    11,    36,   -39,    37,    11,    32,    11,
      28,    11,    -7,   -39,    11,    11,   -39,   -39,   -39,    11,
     -39,   -39,     1,   -39,   -39
};

/* YYPGOTO[NTERM-NUM].  */
static const Int_yysigned_char Int_yypgoto[] =
{
     -39,   -39,   -39,    45,   -39,   -39,   -39,   -39,   -39,   -39,
     -39,   -39,   -39,   -39,   -19,   -22,   -39,   -39,   -39,   -39,
     -10,   -31,   -39,   -39,   -38,   -39,    -1
};

/* YYTABLE[YYPACT[STATE-NUM]].  What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule which
   number is the opposite.  If zero, do what YYDEFACT says.
   If YYTABLE_NINF, syntax error.  */
#define YYTABLE_NINF -1
static const unsigned char Int_yytable[] =
{
      18,    19,    40,    43,    17,    43,    17,    54,    24,    79,
      50,    51,    80,    25,    58,    17,    52,    79,    20,    53,
      84,    26,    27,    33,    44,    22,    44,    31,     1,     2,
       3,     4,     5,    41,    29,    42,     6,    34,    48,    35,
      49,    56,    39,    57,    48,    59,    63,    77,    55,    67,
      75,    48,    69,    28,    71,    60,    82,    83,    62,    76,
      66,     0,    68,     0,     0,     0,    74,     0,    66,     0,
      78,     0,     0,    81,    74,     0,     0,     0,    74
};

static const Int_yysigned_char Int_yycheck[] =
{
       1,     2,    33,     3,     4,     3,     4,    45,    10,    16,
      41,    42,    19,    15,    52,     4,    16,    16,    21,    19,
      19,    14,     0,    24,    24,    20,    24,    17,     5,     6,
       7,     8,     9,    34,    22,    36,    13,    10,    39,    23,
      11,    11,    18,    18,    45,    12,    12,    19,    49,    18,
      18,    52,    16,     8,    17,    56,    75,    79,    59,    69,
      61,    -1,    63,    -1,    -1,    -1,    67,    -1,    69,    -1,
      71,    -1,    -1,    74,    75,    -1,    -1,    -1,    79
};

/* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
   symbol of state STATE-NUM.  */
static const unsigned char Int_yystos[] =
{
       0,     5,     6,     7,     8,     9,    13,    28,    29,    30,
      31,    32,    33,    36,    38,    39,    40,     4,    53,    53,
      21,    43,    20,    49,    10,    15,    14,     0,    30,    22,
      44,    17,    37,    53,    10,    23,    45,    48,    53,    18,
      48,    53,    53,     3,    24,    50,    51,    52,    53,    11,
      48,    48,    16,    19,    51,    53,    11,    18,    51,    12,
      53,    34,    53,    12,    46,    47,    53,    18,    53,    16,
      35,    17,    41,    42,    53,    18,    47,    19,    53,    16,
      19,    53,    41,    42,    19
};

#if ! defined (YYSIZE_T) && defined (__SIZE_TYPE__)
# define YYSIZE_T __SIZE_TYPE__
#endif
#if ! defined (YYSIZE_T) && defined (size_t)
# define YYSIZE_T size_t
#endif
#if ! defined (YYSIZE_T)
# if defined (__STDC__) || defined (__cplusplus)
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# endif
#endif
#if ! defined (YYSIZE_T)
# define YYSIZE_T unsigned int
#endif

#define Int_yyerrok		(Int_yyerrstatus = 0)
#define Int_yyclearin	(Int_yychar = YYEMPTY)
#define YYEMPTY		(-2)
#define YYEOF		0

#define YYACCEPT	goto Int_yyacceptlab
#define YYABORT		goto Int_yyabortlab
#define YYERROR		goto Int_yyerrlab1

/* Like YYERROR except do call Int_yyerror.  This remains here temporarily
   to ease the transition to the new meaning of YYERROR, for GCC.
   Once GCC version 2 has supplanted version 1, this can go.  */

#define YYFAIL		goto Int_yyerrlab

#define YYRECOVERING()  (!!Int_yyerrstatus)

#define YYBACKUP(Token, Value)					\
do								\
  if (Int_yychar == YYEMPTY && Int_yylen == 1)				\
    {								\
      Int_yychar = (Token);						\
      Int_yylval = (Value);						\
      Int_yytoken = YYTRANSLATE (Int_yychar);				\
      YYPOPSTACK;						\
      goto Int_yybackup;						\
    }								\
  else								\
    { 								\
      Int_yyerror ("syntax error: cannot back up");\
      YYERROR;							\
    }								\
while (0)

#define YYTERROR	1
#define YYERRCODE	256

/* YYLLOC_DEFAULT -- Compute the default location (before the actions
   are run).  */

#ifndef YYLLOC_DEFAULT
# define YYLLOC_DEFAULT(Current, Rhs, N)         \
  Current.first_line   = Rhs[1].first_line;      \
  Current.first_column = Rhs[1].first_column;    \
  Current.last_line    = Rhs[N].last_line;       \
  Current.last_column  = Rhs[N].last_column;
#endif

/* YYLEX -- calling `Int_yylex' with the right arguments.  */

#ifdef YYLEX_PARAM
# define YYLEX Int_yylex (YYLEX_PARAM)
#else
# define YYLEX Int_yylex ()
#endif

/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)			\
do {						\
  if (Int_yydebug)					\
    YYFPRINTF Args;				\
} while (0)

# define YYDSYMPRINT(Args)			\
do {						\
  if (Int_yydebug)					\
    Int_yysymprint Args;				\
} while (0)

# define YYDSYMPRINTF(Title, Token, Value, Location)		\
do {								\
  if (Int_yydebug)							\
    {								\
      YYFPRINTF (stderr, "%s ", Title);				\
      Int_yysymprint (stderr, 					\
                  Token, Value);	\
      YYFPRINTF (stderr, "\n");					\
    }								\
} while (0)

/*------------------------------------------------------------------.
| Int_yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (cinluded).                                                   |
`------------------------------------------------------------------*/

#if defined (__STDC__) || defined (__cplusplus)
static void
Int_yy_stack_print (short *bottom, short *top)
#else
static void
Int_yy_stack_print (bottom, top)
    short *bottom;
    short *top;
#endif
{
  YYFPRINTF (stderr, "Stack now");
  for (/* Nothing. */; bottom <= top; ++bottom)
    YYFPRINTF (stderr, " %d", *bottom);
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)				\
do {								\
  if (Int_yydebug)							\
    Int_yy_stack_print ((Bottom), (Top));				\
} while (0)


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

#if defined (__STDC__) || defined (__cplusplus)
static void
Int_yy_reduce_print (int Int_yyrule)
#else
static void
Int_yy_reduce_print (Int_yyrule)
    int Int_yyrule;
#endif
{
  int Int_yyi;
  unsigned int Int_yylineno = Int_yyrline[Int_yyrule];
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %u), ",
             Int_yyrule - 1, Int_yylineno);
  /* Print the symbols being reduced, and their result.  */
  for (Int_yyi = Int_yyprhs[Int_yyrule]; 0 <= Int_yyrhs[Int_yyi]; Int_yyi++)
    YYFPRINTF (stderr, "%s ", Int_yytname [Int_yyrhs[Int_yyi]]);
  YYFPRINTF (stderr, "-> %s\n", Int_yytname [Int_yyr1[Int_yyrule]]);
}

# define YY_REDUCE_PRINT(Rule)		\
do {					\
  if (Int_yydebug)				\
    Int_yy_reduce_print (Rule);		\
} while (0)

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int Int_yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args)
# define YYDSYMPRINT(Args)
# define YYDSYMPRINTF(Title, Token, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef	YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   SIZE_MAX < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#if YYMAXDEPTH == 0
# undef YYMAXDEPTH
#endif

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif



#if YYERROR_VERBOSE

# ifndef Int_yystrlen
#  if defined (__GLIBC__) && defined (_STRING_H)
#   define Int_yystrlen strlen
#  else
/* Return the length of YYSTR.  */
static YYSIZE_T
#   if defined (__STDC__) || defined (__cplusplus)
Int_yystrlen (const char *Int_yystr)
#   else
Int_yystrlen (Int_yystr)
     const char *Int_yystr;
#   endif
{
  register const char *Int_yys = Int_yystr;

  while (*Int_yys++ != '\0')
    continue;

  return Int_yys - Int_yystr - 1;
}
#  endif
# endif

# ifndef Int_yystpcpy
#  if defined (__GLIBC__) && defined (_STRING_H) && defined (_GNU_SOURCE)
#   define Int_yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
static char *
#   if defined (__STDC__) || defined (__cplusplus)
Int_yystpcpy (char *Int_yydest, const char *Int_yysrc)
#   else
Int_yystpcpy (Int_yydest, Int_yysrc)
     char *Int_yydest;
     const char *Int_yysrc;
#   endif
{
  register char *Int_yyd = Int_yydest;
  register const char *Int_yys = Int_yysrc;

  while ((*Int_yyd++ = *Int_yys++) != '\0')
    continue;

  return Int_yyd - 1;
}
#  endif
# endif

#endif /* !YYERROR_VERBOSE */



#if YYDEBUG
/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

#if defined (__STDC__) || defined (__cplusplus)
static void
Int_yysymprint (FILE *Int_yyoutput, int Int_yytype, YYSTYPE *Int_yyvaluep)
#else
static void
Int_yysymprint (Int_yyoutput, Int_yytype, Int_yyvaluep)
    FILE *Int_yyoutput;
    int Int_yytype;
    YYSTYPE *Int_yyvaluep;
#endif
{
  /* Pacify ``unused variable'' warnings.  */
  (void) Int_yyvaluep;

  if (Int_yytype < YYNTOKENS)
    {
      YYFPRINTF (Int_yyoutput, "token %s (", Int_yytname[Int_yytype]);
# ifdef YYPRINT
      YYPRINT (Int_yyoutput, Int_yytoknum[Int_yytype], *Int_yyvaluep);
# endif
    }
  else
    YYFPRINTF (Int_yyoutput, "nterm %s (", Int_yytname[Int_yytype]);

  switch (Int_yytype)
    {
      default:
        break;
    }
  YYFPRINTF (Int_yyoutput, ")");
}

#endif /* ! YYDEBUG */
/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

#if defined (__STDC__) || defined (__cplusplus)
static void
Int_yydestruct (int Int_yytype, YYSTYPE *Int_yyvaluep)
#else
static void
Int_yydestruct (Int_yytype, Int_yyvaluep)
    int Int_yytype;
    YYSTYPE *Int_yyvaluep;
#endif
{
  /* Pacify ``unused variable'' warnings.  */
  (void) Int_yyvaluep;

  switch (Int_yytype)
    {

      default:
        break;
    }
}


/* Prevent warnings from -Wmissing-prototypes.  */

#ifdef YYPARSE_PARAM
# if defined (__STDC__) || defined (__cplusplus)
int Int_yyparse (void *YYPARSE_PARAM);
# else
int Int_yyparse ();
# endif
#else /* ! YYPARSE_PARAM */
#if defined (__STDC__) || defined (__cplusplus)
int Int_yyparse (void);
#else
int Int_yyparse ();
#endif
#endif /* ! YYPARSE_PARAM */



/* The lookahead symbol.  */
int Int_yychar;

/* The semantic value of the lookahead symbol.  */
YYSTYPE Int_yylval;

/* Number of syntax errors so far.  */
int Int_yynerrs;



/*----------.
| Int_yyparse.  |
`----------*/

#ifdef YYPARSE_PARAM
# if defined (__STDC__) || defined (__cplusplus)
int Int_yyparse (void *YYPARSE_PARAM)
# else
int Int_yyparse (YYPARSE_PARAM)
  void *YYPARSE_PARAM;
# endif
#else /* ! YYPARSE_PARAM */
#if defined (__STDC__) || defined (__cplusplus)
int
Int_yyparse (void)
#else
int
Int_yyparse ()

#endif
#endif
{
  
  register int Int_yystate;
  register int Int_yyn;
  int Int_yyresult;
  /* Number of tokens to shift before error messages enabled.  */
  int Int_yyerrstatus;
  /* Lookahead token as an internal (translated) token number.  */
  int Int_yytoken = 0;

  /* Three stacks and their tools:
     `Int_yyss': related to states,
     `Int_yyvs': related to semantic values,
     `Int_yyls': related to locations.

     Refer to the stacks thru separate pointers, to allow Int_yyoverflow
     to reallocate them elsewhere.  */

  /* The state stack.  */
  short	Int_yyssa[YYINITDEPTH];
  short *Int_yyss = Int_yyssa;
  register short *Int_yyssp;

  /* The semantic value stack.  */
  YYSTYPE Int_yyvsa[YYINITDEPTH];
  YYSTYPE *Int_yyvs = Int_yyvsa;
  register YYSTYPE *Int_yyvsp;



#define YYPOPSTACK   (Int_yyvsp--, Int_yyssp--)

  YYSIZE_T Int_yystacksize = YYINITDEPTH;

  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE Int_yyval;


  /* When reducing, the number of symbols on the RHS of the reduced
     rule.  */
  int Int_yylen;

  YYDPRINTF ((stderr, "Starting parse\n"));

  Int_yystate = 0;
  Int_yyerrstatus = 0;
  Int_yynerrs = 0;
  Int_yychar = YYEMPTY;		/* Cause a token to be read.  */

  /* Initialize stack pointers.
     Waste one element of value and location stack
     so that they stay on the same level as the state stack.
     The wasted elements are never initialized.  */

  Int_yyssp = Int_yyss;
  Int_yyvsp = Int_yyvs;

  goto Int_yysetstate;

/*------------------------------------------------------------.
| Int_yynewstate -- Push a new state, which is found in Int_yystate.  |
`------------------------------------------------------------*/
 Int_yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed. so pushing a state here evens the stacks.
     */
  Int_yyssp++;

 Int_yysetstate:
  *Int_yyssp = Int_yystate;

  if (Int_yyss + Int_yystacksize - 1 <= Int_yyssp)
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYSIZE_T Int_yysize = Int_yyssp - Int_yyss + 1;

#ifdef Int_yyoverflow
      {
	/* Give user a chance to reallocate the stack. Use copies of
	   these so that the &'s don't force the real ones into
	   memory.  */
	YYSTYPE *Int_yyvs1 = Int_yyvs;
	short *Int_yyss1 = Int_yyss;


	/* Each stack pointer address is followed by the size of the
	   data in use in that stack, in bytes.  This used to be a
	   conditional around just the two extra args, but that might
	   be undefined if Int_yyoverflow is a macro.  */
	Int_yyoverflow ("parser stack overflow",
		    &Int_yyss1, Int_yysize * sizeof (*Int_yyssp),
		    &Int_yyvs1, Int_yysize * sizeof (*Int_yyvsp),

		    &Int_yystacksize);

	Int_yyss = Int_yyss1;
	Int_yyvs = Int_yyvs1;
      }
#else /* no Int_yyoverflow */
# ifndef YYSTACK_RELOCATE
      goto Int_yyoverflowlab;
# else
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= Int_yystacksize)
	goto Int_yyoverflowlab;
      Int_yystacksize *= 2;
      if (YYMAXDEPTH < Int_yystacksize)
	Int_yystacksize = YYMAXDEPTH;

      {
	short *Int_yyss1 = Int_yyss;
	union Int_yyalloc *Int_yyptr =
	  (union Int_yyalloc *) YYSTACK_ALLOC (YYSTACK_BYTES (Int_yystacksize));
	if (! Int_yyptr)
	  goto Int_yyoverflowlab;
	YYSTACK_RELOCATE (Int_yyss);
	YYSTACK_RELOCATE (Int_yyvs);

#  undef YYSTACK_RELOCATE
	if (Int_yyss1 != Int_yyssa)
	  YYSTACK_FREE (Int_yyss1);
      }
# endif
#endif /* no Int_yyoverflow */

      Int_yyssp = Int_yyss + Int_yysize - 1;
      Int_yyvsp = Int_yyvs + Int_yysize - 1;


      YYDPRINTF ((stderr, "Stack size increased to %lu\n",
		  (unsigned long int) Int_yystacksize));

      if (Int_yyss + Int_yystacksize - 1 <= Int_yyssp)
	YYABORT;
    }

  YYDPRINTF ((stderr, "Entering state %d\n", Int_yystate));

  goto Int_yybackup;

/*-----------.
| Int_yybackup.  |
`-----------*/
Int_yybackup:

/* Do appropriate processing given the current state.  */
/* Read a lookahead token if we need one and don't already have one.  */
/* Int_yyresume: */

  /* First try to decide what to do without reference to lookahead token.  */

  Int_yyn = Int_yypact[Int_yystate];
  if (Int_yyn == YYPACT_NINF)
    goto Int_yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either YYEMPTY or YYEOF or a valid lookahead symbol.  */
  if (Int_yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      Int_yychar = YYLEX;
    }

  if (Int_yychar <= YYEOF)
    {
      Int_yychar = Int_yytoken = YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else
    {
      Int_yytoken = YYTRANSLATE (Int_yychar);
      YYDSYMPRINTF ("Next token is", Int_yytoken, &Int_yylval, &Int_yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  Int_yyn += Int_yytoken;
  if (Int_yyn < 0 || YYLAST < Int_yyn || Int_yycheck[Int_yyn] != Int_yytoken)
    goto Int_yydefault;
  Int_yyn = Int_yytable[Int_yyn];
  if (Int_yyn <= 0)
    {
      if (Int_yyn == 0 || Int_yyn == YYTABLE_NINF)
	goto Int_yyerrlab;
      Int_yyn = -Int_yyn;
      goto Int_yyreduce;
    }

  if (Int_yyn == YYFINAL)
    YYACCEPT;

  /* Shift the lookahead token.  */
  YYDPRINTF ((stderr, "Shifting token %s, ", Int_yytname[Int_yytoken]));

  /* Discard the token being shifted unless it is eof.  */
  if (Int_yychar != YYEOF)
    Int_yychar = YYEMPTY;

  *++Int_yyvsp = Int_yylval;


  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (Int_yyerrstatus)
    Int_yyerrstatus--;

  Int_yystate = Int_yyn;
  goto Int_yynewstate;


/*-----------------------------------------------------------.
| Int_yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
Int_yydefault:
  Int_yyn = Int_yydefact[Int_yystate];
  if (Int_yyn == 0)
    goto Int_yyerrlab;
  goto Int_yyreduce;


/*-----------------------------.
| Int_yyreduce -- Do a reduction.  |
`-----------------------------*/
Int_yyreduce:
  /* Int_yyn is the number of a rule to reduce with.  */
  Int_yylen = Int_yyr2[Int_yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     `$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  Int_yyval = Int_yyvsp[1-Int_yylen];


  YY_REDUCE_PRINT (Int_yyn);
  switch (Int_yyn)
    {
        case 13:
#line 132 "bootparse.y"
    {
					do_start();
					boot_openrel(LexIDStr(Int_yyvsp[0].ival));
					do_end();
				}
    break;

  case 14:
#line 141 "bootparse.y"
    {
					do_start();
					closerel(LexIDStr(Int_yyvsp[0].ival));
					do_end();
				}
    break;

  case 15:
#line 147 "bootparse.y"
    {
					do_start();
					closerel(NULL);
					do_end();
				}
    break;

  case 16:
#line 156 "bootparse.y"
    {
					do_start();
					numattr = 0;
					elog(DEBUG4, "creating%s%s relation %s %u",
						 Int_yyvsp[-5].ival ? " bootstrap" : "",
						 Int_yyvsp[-4].ival ? " shared" : "",
						 LexIDStr(Int_yyvsp[-2].ival),
						 Int_yyvsp[-1].oidval);
				}
    break;

  case 17:
#line 166 "bootparse.y"
    {
					do_end();
				}
    break;

  case 18:
#line 170 "bootparse.y"
    {
					TupleDesc tupdesc;

					do_start();

					tupdesc = CreateTupleDesc(numattr, !(Int_yyvsp[-7].ival), attrtypes);

					if (Int_yyvsp[-9].ival)
					{
						if (boot_reldesc)
						{
							elog(DEBUG4, "create bootstrap: warning, open relation exists, closing first");
							closerel(NULL);
						}

						boot_reldesc = heap_create(LexIDStr(Int_yyvsp[-6].ival),
												   PG_CATALOG_NAMESPACE,
												   Int_yyvsp[-8].ival ? GLOBALTABLESPACE_OID : 0,
												   Int_yyvsp[-5].oidval,
												   tupdesc,
												   RELKIND_RELATION,
												   Int_yyvsp[-8].ival,
												   true);
						elog(DEBUG4, "bootstrap relation created");
					}
					else
					{
						Oid id;

						id = heap_create_with_catalog(LexIDStr(Int_yyvsp[-6].ival),
													  PG_CATALOG_NAMESPACE,
													  Int_yyvsp[-8].ival ? GLOBALTABLESPACE_OID : 0,
													  Int_yyvsp[-5].oidval,
													  BOOTSTRAP_SUPERUSERID,
													  tupdesc,
													  RELKIND_RELATION,
													  Int_yyvsp[-8].ival,
													  true,
													  0,
													  ONCOMMIT_NOOP,
													  true);
						elog(DEBUG4, "relation created with oid %u", id);
					}
					do_end();
				}
    break;

  case 19:
#line 219 "bootparse.y"
    {
					do_start();
					if (Int_yyvsp[0].oidval)
						elog(DEBUG4, "inserting row with oid %u", Int_yyvsp[0].oidval);
					else
						elog(DEBUG4, "inserting row");
					num_columns_read = 0;
				}
    break;

  case 20:
#line 228 "bootparse.y"
    {
					if (num_columns_read != numattr)
						elog(ERROR, "incorrect number of columns in row (expected %d, got %d)",
							 numattr, num_columns_read);
					if (boot_reldesc == NULL)
					{
						elog(ERROR, "relation not open");
						err_out();
					}
					InsertOneTuple(Int_yyvsp[-4].oidval);
					do_end();
				}
    break;

  case 21:
#line 244 "bootparse.y"
    {
					do_start();

					DefineIndex(makeRangeVar(NULL, LexIDStr(Int_yyvsp[-5].ival)),
								LexIDStr(Int_yyvsp[-8].ival),
								Int_yyvsp[-7].oidval,
								LexIDStr(Int_yyvsp[-3].ival),
								NULL,
								Int_yyvsp[-1].list,
								NULL, NIL,
								false, false, false,
								false, false, true, false);
					do_end();
				}
    break;

  case 22:
#line 262 "bootparse.y"
    {
					do_start();

					DefineIndex(makeRangeVar(NULL, LexIDStr(Int_yyvsp[-5].ival)),
								LexIDStr(Int_yyvsp[-8].ival),
								Int_yyvsp[-7].oidval,
								LexIDStr(Int_yyvsp[-3].ival),
								NULL,
								Int_yyvsp[-1].list,
								NULL, NIL,
								true, false, false,
								false, false, true, false);
					do_end();
				}
    break;

  case 23:
#line 280 "bootparse.y"
    {
					do_start();
					build_indices();
					do_end();
				}
    break;

  case 24:
#line 289 "bootparse.y"
    { Int_yyval.list = lappend(Int_yyvsp[-2].list, Int_yyvsp[0].ielem); }
    break;

  case 25:
#line 290 "bootparse.y"
    { Int_yyval.list = list_make1(Int_yyvsp[0].ielem); }
    break;

  case 26:
#line 295 "bootparse.y"
    {
					IndexElem *n = makeNode(IndexElem);
					n->name = LexIDStr(Int_yyvsp[-1].ival);
					n->expr = NULL;
					n->opclass = list_make1(makeString(LexIDStr(Int_yyvsp[0].ival)));
					Int_yyval.ielem = n;
				}
    break;

  case 27:
#line 305 "bootparse.y"
    { Int_yyval.ival = 1; }
    break;

  case 28:
#line 306 "bootparse.y"
    { Int_yyval.ival = 0; }
    break;

  case 29:
#line 310 "bootparse.y"
    { Int_yyval.ival = 1; }
    break;

  case 30:
#line 311 "bootparse.y"
    { Int_yyval.ival = 0; }
    break;

  case 31:
#line 315 "bootparse.y"
    { Int_yyval.ival = 1; }
    break;

  case 32:
#line 316 "bootparse.y"
    { Int_yyval.ival = 0; }
    break;

  case 35:
#line 326 "bootparse.y"
    {
				   if (++numattr > MAXATTR)
						elog(FATAL, "too many columns");
				   DefineAttr(LexIDStr(Int_yyvsp[-2].ival),LexIDStr(Int_yyvsp[0].ival),numattr-1);
				}
    break;

  case 36:
#line 334 "bootparse.y"
    { Int_yyval.oidval = atooid(LexIDStr(Int_yyvsp[0].ival)); }
    break;

  case 37:
#line 338 "bootparse.y"
    { Int_yyval.oidval = Int_yyvsp[0].oidval; }
    break;

  case 38:
#line 339 "bootparse.y"
    { Int_yyval.oidval = (Oid) 0; }
    break;

  case 42:
#line 350 "bootparse.y"
    { InsertOneValue(LexIDStr(Int_yyvsp[0].ival), num_columns_read++); }
    break;

  case 43:
#line 352 "bootparse.y"
    { InsertOneValue(LexIDStr(Int_yyvsp[0].ival), num_columns_read++); }
    break;

  case 44:
#line 354 "bootparse.y"
    { InsertOneNull(num_columns_read++); }
    break;

  case 45:
#line 358 "bootparse.y"
    { Int_yyval.ival=Int_yylval.ival; }
    break;

  case 46:
#line 362 "bootparse.y"
    { Int_yyval.ival=Int_yylval.ival; }
    break;


    }

/* Line 991 of yacc.c.  */
#line 1443 "y.tab.c"

  Int_yyvsp -= Int_yylen;
  Int_yyssp -= Int_yylen;


  YY_STACK_PRINT (Int_yyss, Int_yyssp);

  *++Int_yyvsp = Int_yyval;


  /* Now `shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */

  Int_yyn = Int_yyr1[Int_yyn];

  Int_yystate = Int_yypgoto[Int_yyn - YYNTOKENS] + *Int_yyssp;
  if (0 <= Int_yystate && Int_yystate <= YYLAST && Int_yycheck[Int_yystate] == *Int_yyssp)
    Int_yystate = Int_yytable[Int_yystate];
  else
    Int_yystate = Int_yydefgoto[Int_yyn - YYNTOKENS];

  goto Int_yynewstate;


/*------------------------------------.
| Int_yyerrlab -- here on detecting error |
`------------------------------------*/
Int_yyerrlab:
  /* If not already recovering from an error, report this error.  */
  if (!Int_yyerrstatus)
    {
      ++Int_yynerrs;
#if YYERROR_VERBOSE
      Int_yyn = Int_yypact[Int_yystate];

      if (YYPACT_NINF < Int_yyn && Int_yyn < YYLAST)
	{
	  YYSIZE_T Int_yysize = 0;
	  int Int_yytype = YYTRANSLATE (Int_yychar);
	  char *Int_yymsg;
	  int Int_yyx, Int_yycount;

	  Int_yycount = 0;
	  /* Start YYX at -YYN if negative to avoid negative indexes in
	     YYCHECK.  */
	  for (Int_yyx = Int_yyn < 0 ? -Int_yyn : 0;
	       Int_yyx < (int) (sizeof (Int_yytname) / sizeof (char *)); Int_yyx++)
	    if (Int_yycheck[Int_yyx + Int_yyn] == Int_yyx && Int_yyx != YYTERROR)
	      Int_yysize += Int_yystrlen (Int_yytname[Int_yyx]) + 15, Int_yycount++;
	  Int_yysize += Int_yystrlen ("syntax error, unexpected ") + 1;
	  Int_yysize += Int_yystrlen (Int_yytname[Int_yytype]);
	  Int_yymsg = (char *) YYSTACK_ALLOC (Int_yysize);
	  if (Int_yymsg != 0)
	    {
	      char *Int_yyp = Int_yystpcpy (Int_yymsg, "syntax error, unexpected ");
	      Int_yyp = Int_yystpcpy (Int_yyp, Int_yytname[Int_yytype]);

	      if (Int_yycount < 5)
		{
		  Int_yycount = 0;
		  for (Int_yyx = Int_yyn < 0 ? -Int_yyn : 0;
		       Int_yyx < (int) (sizeof (Int_yytname) / sizeof (char *));
		       Int_yyx++)
		    if (Int_yycheck[Int_yyx + Int_yyn] == Int_yyx && Int_yyx != YYTERROR)
		      {
			const char *Int_yyq = ! Int_yycount ? ", expecting " : " or ";
			Int_yyp = Int_yystpcpy (Int_yyp, Int_yyq);
			Int_yyp = Int_yystpcpy (Int_yyp, Int_yytname[Int_yyx]);
			Int_yycount++;
		      }
		}
	      Int_yyerror (Int_yymsg);
	      YYSTACK_FREE (Int_yymsg);
	    }
	  else
	    Int_yyerror ("syntax error; also virtual memory exhausted");
	}
      else
#endif /* YYERROR_VERBOSE */
	Int_yyerror ("syntax error");
    }



  if (Int_yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
	 error, discard it.  */

      /* Return failure if at end of input.  */
      if (Int_yychar == YYEOF)
        {
	  /* Pop the error token.  */
          YYPOPSTACK;
	  /* Pop the rest of the stack.  */
	  while (Int_yyss < Int_yyssp)
	    {
	      YYDSYMPRINTF ("Error: popping", Int_yystos[*Int_yyssp], Int_yyvsp, Int_yylsp);
	      Int_yydestruct (Int_yystos[*Int_yyssp], Int_yyvsp);
	      YYPOPSTACK;
	    }
	  YYABORT;
        }

      YYDSYMPRINTF ("Error: discarding", Int_yytoken, &Int_yylval, &Int_yylloc);
      Int_yydestruct (Int_yytoken, &Int_yylval);
      Int_yychar = YYEMPTY;

    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto Int_yyerrlab2;


/*----------------------------------------------------.
| Int_yyerrlab1 -- error raised explicitly by an action.  |
`----------------------------------------------------*/
Int_yyerrlab1:

  /* Suppress GCC warning that Int_yyerrlab1 is unused when no action
     invokes YYERROR.  */
#if defined (__GNUC_MINOR__) && 2093 <= (__GNUC__ * 1000 + __GNUC_MINOR__)
  __attribute__ ((__unused__))
#endif


  goto Int_yyerrlab2;


/*---------------------------------------------------------------.
| Int_yyerrlab2 -- pop states until the error token can be shifted.  |
`---------------------------------------------------------------*/
Int_yyerrlab2:
  Int_yyerrstatus = 3;	/* Each real token shifted decrements this.  */

  for (;;)
    {
      Int_yyn = Int_yypact[Int_yystate];
      if (Int_yyn != YYPACT_NINF)
	{
	  Int_yyn += YYTERROR;
	  if (0 <= Int_yyn && Int_yyn <= YYLAST && Int_yycheck[Int_yyn] == YYTERROR)
	    {
	      Int_yyn = Int_yytable[Int_yyn];
	      if (0 < Int_yyn)
		break;
	    }
	}

      /* Pop the current state because it cannot handle the error token.  */
      if (Int_yyssp == Int_yyss)
	YYABORT;

      YYDSYMPRINTF ("Error: popping", Int_yystos[*Int_yyssp], Int_yyvsp, Int_yylsp);
      Int_yydestruct (Int_yystos[Int_yystate], Int_yyvsp);
      Int_yyvsp--;
      Int_yystate = *--Int_yyssp;

      YY_STACK_PRINT (Int_yyss, Int_yyssp);
    }

  if (Int_yyn == YYFINAL)
    YYACCEPT;

  YYDPRINTF ((stderr, "Shifting error token, "));

  *++Int_yyvsp = Int_yylval;


  Int_yystate = Int_yyn;
  goto Int_yynewstate;


/*-------------------------------------.
| Int_yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
Int_yyacceptlab:
  Int_yyresult = 0;
  goto Int_yyreturn;

/*-----------------------------------.
| Int_yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
Int_yyabortlab:
  Int_yyresult = 1;
  goto Int_yyreturn;

#ifndef Int_yyoverflow
/*----------------------------------------------.
| Int_yyoverflowlab -- parser overflow comes here.  |
`----------------------------------------------*/
Int_yyoverflowlab:
  Int_yyerror ("parser stack overflow");
  Int_yyresult = 2;
  /* Fall through.  */
#endif

Int_yyreturn:
#ifndef Int_yyoverflow
  if (Int_yyss != Int_yyssa)
    YYSTACK_FREE (Int_yyss);
#endif
  return Int_yyresult;
}


#line 364 "bootparse.y"


#include "bootscanner.c"

