#detect cudd setup, as it is shared between different installations.

find_package(CUDD)
#  CUDD_FOUND       - system has CUDD 
#  CUDD_LIBRARIES   - Link these to use CUDD
#  CUDD_INCLUDE_DIR - Include directory for using CUDD
#

macro_log_feature (CUDD_FOUND "CUDD"
  "Use CUDD Library"
  "http://vlsi.colorado.edu/~fabio/CUDD/" FALSE)

check_include_files( cudd.h HAVE_CUDD_H )
check_include_files( "stdio.h;cudd/cudd.h" HAVE_CUDD_CUDD_H )
check_include_files( cuddInt.h HAVE_CUDDINT_H )
check_include_files( "stdio.h;cudd/cudd.h;cudd/cuddInt.h" HAVE_CUDD_CUDDINT_H )


