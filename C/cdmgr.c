/*************************************************************************
*									 *
*	 YAP Prolog 							 *
*									 *
*	Yap Prolog was developed at NCCUP - Universidade do Porto	 *
*									 *
* Copyright L.Damas, V.S.Costa and Universidade do Porto 1985-1997	 *
*									 *
**************************************************************************
*									 *
* File:		cdmgr.c							 *
* Last rev:	8/2/88							 *
* mods:									 *
* comments:	Code manager						 *
*									 *
*************************************************************************/
#ifdef SCCS
static char     SccsId[] = "@(#)cdmgr.c	1.1 05/02/98";
#endif

#include "Yap.h"
#include "clause.h"
#include "yapio.h"
#include "eval.h"
#include "tracer.h"
#ifdef YAPOR
#include "or.macros.h"
#endif	/* YAPOR */
#if HAVE_STRING_H
#include <string.h>
#endif


STATIC_PROTO(void retract_all, (PredEntry *));
STATIC_PROTO(void add_first_static, (PredEntry *, CODEADDR, int));
STATIC_PROTO(void add_first_dynamic, (PredEntry *, CODEADDR, int));
STATIC_PROTO(void asserta_stat_clause, (PredEntry *, CODEADDR, int));
STATIC_PROTO(void asserta_dynam_clause, (PredEntry *, CODEADDR));
STATIC_PROTO(void assertz_stat_clause, (PredEntry *, CODEADDR, int));
STATIC_PROTO(void assertz_dynam_clause, (PredEntry *, CODEADDR));
STATIC_PROTO(void expand_consult, (void));
STATIC_PROTO(int  not_was_reconsulted, (PredEntry *, Term, int));
#if EMACS
STATIC_PROTO(int  last_clause_number, (PredEntry *));
#endif
STATIC_PROTO(int  static_in_use, (PredEntry *, int));
#if !defined(YAPOR) && !defined(THREADS)
STATIC_PROTO(Int  search_for_static_predicate_in_use, (PredEntry *, int));
STATIC_PROTO(void mark_pred, (int, PredEntry *));
STATIC_PROTO(void do_toggle_static_predicates_in_use, (int));
#endif
STATIC_PROTO(void recover_log_upd_clause, (Clause *));
STATIC_PROTO(Int  p_number_of_clauses, (void));
STATIC_PROTO(Int  p_compile, (void));
STATIC_PROTO(Int  p_compile_dynamic, (void));
STATIC_PROTO(Int  p_purge_clauses, (void));
STATIC_PROTO(Int  p_setspy, (void));
STATIC_PROTO(Int  p_rmspy, (void));
STATIC_PROTO(Int  p_startconsult, (void));
STATIC_PROTO(Int  p_showconslultlev, (void));
STATIC_PROTO(Int  p_endconsult, (void));
STATIC_PROTO(Int  p_undefined, (void));
STATIC_PROTO(Int  p_in_use, (void));
STATIC_PROTO(Int  p_new_multifile, (void));
STATIC_PROTO(Int  p_is_multifile, (void));
STATIC_PROTO(Int  p_optimizer_on, (void));
STATIC_PROTO(Int  p_optimizer_off, (void));
STATIC_PROTO(Int  p_in_this_f_before, (void));
STATIC_PROTO(Int  p_first_cl_in_f, (void));
STATIC_PROTO(Int  p_mk_cl_not_first, (void));
STATIC_PROTO(Int  p_is_dynamic, (void));
STATIC_PROTO(Int  p_kill_dynamic, (void));
STATIC_PROTO(Int  p_compile_mode, (void));
STATIC_PROTO(Int  p_is_profiled, (void));
STATIC_PROTO(Int  p_profile_info, (void));
STATIC_PROTO(Int  p_profile_reset, (void));
STATIC_PROTO(Int  p_toggle_static_predicates_in_use, (void));
#ifdef DEBUG
STATIC_PROTO(void  list_all_predicates_in_use, (void));
#endif

#define PredArity(p) (p->ArityOfPE)
#define TRYCODE(G,F,N) ( (N)<5 ? (op_numbers)((int)F+(N)*3) : G)
#define NEXTOP(V,TYPE)    ((yamop *)(&((V)->u.TYPE.next)))

static int      compile_mode = 1;

static char     ErrorSay[256];

/******************************************************************
  
			EXECUTING PROLOG CLAUSES
  
******************************************************************/


static int 
static_in_use(PredEntry *p, int check_everything)
{
#if defined(YAPOR) || defined(THREADS)
  return(FALSE);
#else
  CELL pflags = p->PredFlags;
  if (pflags & (DynamicPredFlag|LogUpdatePredFlag)) {
    return (FALSE);
  }
  if (STATIC_PREDICATES_MARKED) {
    return (p->StateOfPred & InUseMask);
  } else {
    /* This code does not work for YAPOR or THREADS!!!!!!!! */
    return(search_for_static_predicate_in_use(p, TRUE /*check_everything*/));
  }
#endif
}

/******************************************************************
  
		ADDING AND REMOVE INFO TO A PROCEDURE
  
******************************************************************/


/*
 * we have three kinds of predicates: dynamic		DynamicPredFlag
 * static 		CompiledPredFlag fast		FastPredFlag all the
 * database predicates are supported for dynamic predicates only abolish and
 * assertz are supported for static predicates no database predicates are
 * supportted for fast predicates 
 */

#define is_dynamic(pe)  (pe->PredFlags & DynamicPredFlag)
#define is_static(pe) 	(pe->PredFlags & CompiledPredFlag)
#define is_fast(pe)	(pe->PredFlags & FastPredFlag)
#define is_logupd(pe)	(pe->PredFlags & LogUpdatePredFlag)
#ifdef TABLING
#define is_tabled(pe)   (pe->PredFlags & TabledPredFlag)
#endif /* TABLING */

/******************************************************************
  
		Indexation Info
  
******************************************************************/
#define ByteAdr(X)   ((Int) &(X))

/* Index a prolog pred, given its predicate entry */
/* ap is already locked, but IPred is the one who gets rid of the lock. */
void 
IPred(CODEADDR sp)
{
  PredEntry      *ap;
  CODEADDR        BaseAddr;
  int             Arity;
  Functor         f;

  ap = (PredEntry *) sp;
#ifdef TABLING
  if (is_tabled(ap)) {
    ap->CodeOfPred = ap->TrueCodeOfPred;
    ap->OpcodeOfPred = ((yamop *)(ap->CodeOfPred))->opc;
    return;
  }
#endif /* TABLING */
  f = ap->FunctorOfPred;
#ifdef DEBUG
  if (Option['i' - 'a' + 1]) {
    Atom At = NameOfFunctor(f);
    DebugPutc(c_output_stream,'\t');
    plwrite(MkAtomTerm(At), DebugPutc, 0);
    DebugPutc(c_output_stream,'/');
    plwrite(MkIntTerm(ArityOfFunctor(f)), DebugPutc, 0);
    DebugPutc(c_output_stream,'\n');
  }
#endif
  Arity = ArityOfFunctor(f);
  /* Do not try to index a dynamic predicate  or one whithout args */
  if (is_dynamic(ap)) {
    WRITE_UNLOCK(ap->PRWLock);
    Error(SYSTEM_ERROR,TermNil,"trying to index a dynamic predicate");
    return;
  }
  if (Arity == 0) {
    WRITE_UNLOCK(ap->PRWLock);
    Error(SYSTEM_ERROR,TermNil,
	  "trying to index a predicate with 0 arguments");
    return;
  }
  if ((BaseAddr = PredIsIndexable(ap)) != NIL) {
    ap->TrueCodeOfPred = BaseAddr;
    ap->PredFlags |= IndexedPredFlag;
  }
  if (ap->PredFlags & SpiedPredFlag) {
    ap->StateOfPred = StaticMask | SpiedMask;
    ap->OpcodeOfPred = opcode(_spy_pred);
    ap->CodeOfPred = (CODEADDR)(&(ap->OpcodeOfPred)); 
  } else {
    ap->StateOfPred = 0;
    ap->CodeOfPred = ap->TrueCodeOfPred;
    ap->OpcodeOfPred = ((yamop *)(ap->CodeOfPred))->opc;
  }
  WRITE_UNLOCK(ap->PRWLock);
#ifdef DEBUG
  if (Option['i' - 'a' + 1])
    DebugPutc(c_output_stream,'\n');
#endif
}


#define GONEXT(TYPE)      code_p = ((yamop *)(&(code_p->u.TYPE.next)))

static void
recover_log_upd_clause(Clause *cl)
{
  LOCK(cl->ClLock);
  if (cl->ClFlags & LogUpdRuleMask) {
    if (--(cl->u2.ClExt->u.EC.ClRefs) == 0 &&
	(cl->ClFlags & ErasedMask) &&
#if defined(YAPOR) || defined(THREADS)
	(cl->ref_count == 0)
#else
	!(cl->ClFlags & InUseMask)
#endif
	)
      ErCl(cl);
  } else {
    if (--(cl->u2.ClUse) == 0 &&
	(cl->ClFlags & ErasedMask) &&
#if defined(YAPOR) || defined(THREADS)
	(cl->ref_count == 0)
#else
	!(cl->ClFlags & InUseMask)
#endif
	)
      ErCl(cl);
  }
  UNLOCK(cl->ClLock);
}

static Clause *
ClauseBodyToClause(CODEADDR addr)
{
  addr = addr - (Int)NEXTOP((yamop *)NULL,ld);
  return(ClauseCodeToClause(addr));
}

/* we already have a lock on the predicate */
void
RemoveLogUpdIndex(Clause *cl)
{
  yamop *code_p;
  OPCODE last = opcode(_trust_logical_pred);

#if defined(YAPOR) || defined(THREADS)
  if (cl->ref_count != 0)
    return;  
#else
  if (cl->ClFlags & InUseMask)
    return;
#endif
  /* now the hard part, I must tell all other clauses they are free */
  code_p = cl->u.ClVarChain;
  /* skip try_log_update */
  GONEXT(l);
  recover_log_upd_clause(ClauseBodyToClause(code_p->u.ld.d));
  GONEXT(ld);
  while(code_p->opc != last) {
    recover_log_upd_clause(ClauseBodyToClause(code_p->u.ld.d));
    GONEXT(ld);
  }
  /* skip trust_log_update */
  GONEXT(l);
  recover_log_upd_clause(ClauseBodyToClause(code_p->u.ld.d));
  FreeCodeSpace((char *) cl);
}

/* Routine used when wanting to remove the indexation */
/* ap is known to already have been locked for WRITING */
int 
RemoveIndexation(PredEntry *ap)
{ 
  register CODEADDR First;
  int             spied;

  First = ap->FirstClause;
  if (ap->OpcodeOfPred == INDEX_OPCODE) {
    return (TRUE);
  }
  spied = ap->PredFlags & SpiedPredFlag;
  if (ap->PredFlags & LogUpdatePredFlag) 
    RemoveLogUpdIndex(ClauseCodeToClause(ap->TrueCodeOfPred));
  else {
    Clause *cl = ClauseCodeToClause(ap->TrueCodeOfPred);
    if (static_in_use(ap, TRUE)) {
      Int Arity = ap->ArityOfPE;

      ErrorMessage = ErrorSay;
      Error_Term = TermNil;
      Error_TYPE = PERMISSION_ERROR_MODIFY_STATIC_PROCEDURE;
      if (Arity == 0)
	sprintf(ErrorMessage, "predicate %s is in use", RepAtom((Atom)(ap->FunctorOfPred))->StrOfAE);
      else
	sprintf(ErrorMessage,
#if SHORT_INTS
		"predicate %s/%ld is in use",
#else
		"predicate %s/%d is in use",
#endif
		RepAtom(NameOfFunctor(ap->FunctorOfPred))->StrOfAE, Arity);
      return(FALSE);
    } else {
      FreeCodeSpace((char *)cl);
    }
  }
  if (First != ap->LastClause)
    ap->TrueCodeOfPred = First;
  ap->PredFlags ^= IndexedPredFlag;
  if (First != NIL && spied) {
    ap->OpcodeOfPred = opcode(_spy_pred);
    ap->CodeOfPred = (CODEADDR)(&(ap->OpcodeOfPred)); 
    ap->StateOfPred = StaticMask | SpiedMask;
  } else {
    ap->StateOfPred = StaticMask;
    ap->OpcodeOfPred = ((yamop *)(ap->TrueCodeOfPred))->opc;
    ap->CodeOfPred = ap->TrueCodeOfPred;
  }
  return (TRUE);
}

/******************************************************************
  
			Adding clauses
  
******************************************************************/


#define	assertz	0
#define	consult	1
#define	asserta	2

/* p is already locked */
static void 
retract_all(PredEntry *p)
{
  CODEADDR        q, q1;
  int             multifile_pred = p->PredFlags & MultiFileFlag;
  CODEADDR        fclause = NIL, lclause = NIL;

  q = p->FirstClause;
  if (q != NIL) {
    do {
      Clause *cl;
      q1 = q;
      q = NextClause(q);
      cl = ClauseCodeToClause(q1);
      if (multifile_pred && cl->Owner != YapConsultingFile()) {
	if (fclause == NIL) {
	  fclause = q1;
	} else {
	  yamop *clp = (yamop *)lclause;
	  clp->u.ld.d = q1;
	}
	lclause = q1;
      } else {
	if (p->PredFlags & LogUpdatePredFlag)
	  ErCl(cl);
	else
	  FreeCodeSpace((char *)cl);
      }
    } while (q1 != p->LastClause);
  }
  p->FirstClause = fclause;
  p->LastClause = lclause;
  if (fclause == NIL) {
    p->OpcodeOfPred = UNDEF_OPCODE;
    p->TrueCodeOfPred = p->CodeOfPred = (CODEADDR)(&(p->OpcodeOfPred)); 
    p->StatisticsForPred.NOfEntries = 0;
    p->StatisticsForPred.NOfHeadSuccesses = 0;
    p->StatisticsForPred.NOfRetries = 0;
  } else {
    yamop *cpt = (yamop *)fclause;
    cpt->opc = opcode(TRYCODE(_try_me, _try_me0, PredArity(p)));
    if (fclause == lclause) {
      p->TrueCodeOfPred = p->CodeOfPred = (CODEADDR)NEXTOP(cpt,ld);
      p->OpcodeOfPred = NEXTOP(cpt,ld)->opc;
    } else {
      p->TrueCodeOfPred = p->CodeOfPred = fclause;
      p->OpcodeOfPred = cpt->opc;
      if (p->PredFlags & ProfiledPredFlag) {
	((yamop *)lclause)->opc = opcode(_profiled_trust_me);
      } else {
	((yamop *)lclause)->opc = opcode(TRYCODE(_trust_me, _trust_me0, PredArity(p)));
      }
    }
    if (p->PredFlags & SpiedPredFlag) {
      p->StateOfPred |= StaticMask | SpiedMask;
      p->OpcodeOfPred = opcode(_spy_pred);
      p->CodeOfPred = (CODEADDR)(&(p->OpcodeOfPred)); 
    } else if (p->PredFlags & IndexedPredFlag) {
      p->OpcodeOfPred = INDEX_OPCODE;
      p->CodeOfPred = (CODEADDR)(&(p->OpcodeOfPred)); 
    }
  }
  if (PROFILING) {
    p->PredFlags |= ProfiledPredFlag;
  } else
    p->PredFlags &= ~ProfiledPredFlag;
#ifdef YAPOR
  if (SEQUENTIAL_IS_DEFAULT) {
    p->PredFlags |= SequentialPredFlag;
  }
#endif /* YAPOR */
  PutValue(AtomAbol, MkAtomTerm(AtomTrue));
}

/* p is already locked */
static void 
add_first_static(PredEntry *p, CODEADDR cp, int spy_flag)
{
  yamop *pt = (yamop *)cp;

  pt->u.ld.d = cp;
  pt->u.ld.p = (CODEADDR)p;
#ifdef YAPOR
  if (SEQUENTIAL_IS_DEFAULT) {
    p->PredFlags |= SequentialPredFlag;
    PUT_YAMOP_SEQ(pt);
  }
  if (YAMOP_LTT(pt) != 1)
    abort_optyap("YAMOP_LTT error in function add_first_static");
#endif /* YAPOR */
#ifdef TABLING
  if (is_tabled(p)) {
    pt->u.ld.te = p->TableOfPred;
    pt->opc = opcode(_table_try_me_single);
  }
  else	
#endif /* TABLING */
    {
      pt->opc = opcode(TRYCODE(_try_me, _try_me0, PredArity(p)));
      pt = NEXTOP(pt, ld);
    }
  p->TrueCodeOfPred = (CODEADDR)pt;
  p->FirstClause = p->LastClause = cp;
  p->StatisticsForPred.NOfEntries = 0;
  p->StatisticsForPred.NOfHeadSuccesses = 0;
  p->StatisticsForPred.NOfRetries = 0;
  if (PROFILING) {
    p->PredFlags |= ProfiledPredFlag;
  } else
    p->PredFlags &= ~ProfiledPredFlag;
#ifdef YAPOR
  p->PredFlags |= SequentialPredFlag;
  PUT_YAMOP_SEQ((yamop *)cp);
#endif /* YAPOR */
  if (spy_flag) {
    p->StateOfPred |= StaticMask | SpiedMask;
    p->OpcodeOfPred = opcode(_spy_pred);
    p->CodeOfPred = (CODEADDR)(&(p->OpcodeOfPred)); 
  } else if (is_fast(p)) {
    p->StateOfPred |= StaticMask;
  } else {
    p->StateOfPred |= StaticMask;
  }
  if (yap_flags[SOURCE_MODE_FLAG]) {
    p->PredFlags |= SourcePredFlag;
  } else {
    p->PredFlags &= ~SourcePredFlag;
  }
}

/* p is already locked */
static void 
add_first_dynamic(PredEntry *p, CODEADDR cp, int spy_flag)
{
  yamop    *ncp = ((Clause *)NIL)->ClCode;
  Clause   *cl;
  p->StatisticsForPred.NOfEntries = 0;
  p->StatisticsForPred.NOfHeadSuccesses = 0;
  p->StatisticsForPred.NOfRetries = 0;
  if (PROFILING) {
    p->PredFlags |= ProfiledPredFlag;
  } else
    p->PredFlags &= ~ProfiledPredFlag;
#ifdef YAPOR
  p->PredFlags |= SequentialPredFlag;
#endif /* YAPOR */
  /* allocate starter block, containing info needed to start execution,
   * that is a try_mark to start the code and a fail to finish things up */
  cl =
    (Clause *) AllocCodeSpace((Int)NEXTOP(NEXTOP(NEXTOP(ncp,ld),e),e));
  if (cl == NIL) {
    Error(SYSTEM_ERROR,TermNil,"Heap crashed against Stacks");
    return;
  }
  cl->Owner = p->OwnerFile;
  /* skip the first entry, this contains the back link and will always be
     empty for this entry */
  ncp = (yamop *)(((CELL *)ncp)+1);
  /* next we have the flags. For this block mainly say whether we are
   *  being spied */
  if (spy_flag) {
    cl->ClFlags = DynamicMask | SpiedMask;
    ncp = cl->ClCode;
  }
  else {
    cl->ClFlags = DynamicMask;
    ncp = cl->ClCode;
  }
  INIT_LOCK(cl->ClLock);
  INIT_CLREF_COUNT(cl);
  /* next, set the first instruction to execute in the dyamic
   *  predicate */
  if (spy_flag)
    p->OpcodeOfPred = ncp->opc = opcode(_spy_or_trymark);
  else
    p->OpcodeOfPred = ncp->opc = opcode(_try_and_mark);
  ncp->u.ld.s = p->ArityOfPE;
  ncp->u.ld.p = (CODEADDR)p;
  ncp->u.ld.d = cp;
#ifdef YAPOR
  INIT_YAMOP_LTT(ncp, 1);
  PUT_YAMOP_SEQ(ncp);
#endif /* YAPOR */
  /* This is the point we enter the code */
  p->TrueCodeOfPred = p->CodeOfPred = (CODEADDR)ncp;
  /* set the first clause to have a retry and mark which will
   *  backtrack to the previous block */
  if (p->PredFlags & ProfiledPredFlag)
    ((yamop *)cp)->opc = opcode(_profiled_retry_and_mark);
  else
    ((yamop *)cp)->opc = opcode(_retry_and_mark);
  ((yamop *)cp)->u.ld.s = p->ArityOfPE;
  ((yamop *)cp)->u.ld.p = (CODEADDR)p;
  ((yamop *)cp)->u.ld.d = (CODEADDR)ncp;
#ifdef KEEP_ENTRY_AGE
  /* also, keep a backpointer for the days you delete the clause */
  ClauseCodeToClause(cp)->u.ClPrevious = ncp;
#endif
  /* Don't forget to say who is the only clause for the predicate so
     far */
  p->LastClause = p->FirstClause = cp;
  /* we're only missing what to do when we actually exit the procedure
   */
  ncp = NEXTOP(ncp,ld);
  /* and the last instruction to execute to exit the predicate, note
     the retry is pointing to this pseudo clause */
  ncp->opc = opcode(_trust_fail);
  /* we're only missing what to do when we actually exit the procedure
   */
  /* and close the code */
  ncp = NEXTOP(ncp,e);
  ncp->opc = opcode(_Ystop);
}

/* p is already locked */
static void 
asserta_stat_clause(PredEntry *p, CODEADDR cp, int spy_flag)
{
  yamop        *q = (yamop *)cp;
  q->u.ld.d = p->FirstClause;
  q->u.ld.p = (CODEADDR)p;
#ifdef YAPOR
  PUT_YAMOP_LTT(q, YAMOP_LTT((yamop *)(p->FirstClause)) + 1);
#endif /* YAPOR */
#ifdef TABLING
  if (is_tabled(p))
    q->opc = opcode(_table_try_me);    
  else
#endif /* TABLING */
    q->opc = opcode(TRYCODE(_try_me, _try_me0, PredArity(p)));
  q = (yamop *)(p->FirstClause);
  if (p->PredFlags & ProfiledPredFlag) {
    if (p->FirstClause == p->LastClause)
      q->opc = opcode(_profiled_trust_me);
    else
      q->opc = opcode(_profiled_retry_me);
  } else {
    if (p->FirstClause == p->LastClause) {
#ifdef TABLING
      if (is_tabled(p))
	q->opc = opcode(_table_trust_me);    
      else
#endif /* TABLING */
	q->opc = opcode(TRYCODE(_trust_me, _trust_me0, PredArity(p)));
    } else {
#ifdef TABLING
      if (is_tabled(p))
	q->opc = opcode(_table_retry_me);    
      else
#endif /* TABLING */
      q->opc = opcode(TRYCODE(_retry_me, _retry_me0, PredArity(p)));
    }
  }
  p->TrueCodeOfPred = p->FirstClause = cp;
  q = ((yamop *)p->LastClause);
  q->u.ld.d = cp;
}

/* p is already locked */
static void 
asserta_dynam_clause(PredEntry *p, CODEADDR cp)
{
  yamop        *q;
  q = (yamop *)cp;
  LOCK(ClauseCodeToClause(p->FirstClause)->ClLock);
#ifdef KEEP_ENTRY_AGE
  /* also, keep backpointers for the days we'll delete all the clause */
  ClauseCodeToClause(p->FirstClause)->u.ClPrevious = q;
  ClauseCodeToClause(cp)->u.ClPrevious = (yamop *)(p->CodeOfPred);
#endif
  UNLOCK(ClauseCodeToClause(p->FirstClause)->ClLock);
  q->u.ld.d = p->FirstClause;
  q->u.ld.s = p->ArityOfPE;
  q->u.ld.p = (CODEADDR)p;
  if (p->PredFlags & ProfiledPredFlag)
    ((yamop *)cp)->opc = opcode(_retry_and_mark);
  else
    ((yamop *)cp)->opc = opcode(_profiled_retry_and_mark);
  ((yamop *)cp)->u.ld.s = p->ArityOfPE;
  ((yamop *)cp)->u.ld.p = (CODEADDR)p;
  p->FirstClause = cp;
  q = (yamop *)p->CodeOfPred;
  q->u.ld.d = cp;
  q->u.ld.s = p->ArityOfPE;
  q->u.ld.p = (CODEADDR)p;
}

/* p is already locked */
static void 
assertz_stat_clause(PredEntry *p, CODEADDR cp, int spy_flag)
{
  yamop        *pt;
  pt = (yamop *)(p->LastClause);
  if (p->PredFlags & ProfiledPredFlag) {
    if (p->FirstClause == p->LastClause) {
      pt->opc = opcode(TRYCODE(_try_me, _try_me0, PredArity(p)));
      p->TrueCodeOfPred = p->FirstClause;
    } else
      pt->opc = opcode(_profiled_retry_me);
  } else {
    if (p->FirstClause == p->LastClause) {
#ifdef TABLING
      if (is_tabled(p))
	pt->opc = opcode(_table_try_me);    
      else
#endif /* TABLING */
	pt->opc = opcode(TRYCODE(_try_me, _try_me0, PredArity(p)));
      p->TrueCodeOfPred = p->FirstClause;
    } else {
#ifdef TABLING
      if (is_tabled(p))
	pt->opc = opcode(_table_retry_me);    
      else
#endif /* TABLING */
	pt->opc = opcode(TRYCODE(_retry_me, _retry_me0, PredArity(p)));
    }
  }
  pt->u.ld.d = cp;
  p->LastClause = cp;
  pt = (yamop *)cp;
  if (p->PredFlags & ProfiledPredFlag) {
    pt->opc = opcode(_profiled_trust_me);
  } else {
#ifdef TABLING
    if (is_tabled(p))
      pt->opc = opcode(_table_trust_me);    
    else
#endif /* TABLING */
      pt->opc = opcode(TRYCODE(_trust_me, _trust_me0, PredArity(p)));
  }
  pt->u.ld.d = p->FirstClause;
#ifdef YAPOR
  {
    CODEADDR code;

    code = p->FirstClause;
    while (code != p->LastClause){
      PUT_YAMOP_LTT((yamop *)code, YAMOP_LTT((yamop *)code) + 1);
      code = NextClause(code);
    }
  }
#endif /* YAPOR */
}

/* p is already locked */
static void 
assertz_dynam_clause(PredEntry *p, CODEADDR cp)
{
  yamop       *q;

  q = (yamop *)(p->LastClause);
  LOCK(ClauseCodeToClause(q)->ClLock);
  q->u.ld.d = cp;
  p->LastClause = cp;
#ifdef KEEP_ENTRY_AGE
  /* also, keep backpointers for the days we'll delete all the clause */
  ClauseCodeToClause(cp)->u.ClPrevious = q;
#endif
  UNLOCK(ClauseCodeToClause(q)->ClLock);
  q = (yamop *)cp;
  if (p->PredFlags & ProfiledPredFlag)
    q->opc = opcode(_profiled_retry_and_mark);
  else
    q->opc = opcode(_retry_and_mark);
  q->u.ld.d = p->CodeOfPred;
  q->u.ld.s = p->ArityOfPE;
  q->u.ld.p = (CODEADDR)p;
}

static void  expand_consult(void)
{
  consult_obj *new_cl, *new_cb, *new_cs;
  UInt OldConsultCapacity = ConsultCapacity;

  /* now double consult capacity */
  ConsultCapacity += InitialConsultCapacity;
  /* I assume it always works ;-) */
  new_cl = (consult_obj *)AllocCodeSpace(sizeof(consult_obj)*ConsultCapacity);
  if (new_cl == NULL) {
    Error(SYSTEM_ERROR,TermNil,"Could not expand consult space: Heap crashed against Stacks");
    return;
  }
  new_cs = new_cl + (InitialConsultCapacity+1);
  new_cb = new_cs + (ConsultBase-ConsultSp);
  /* start copying */
  memcpy((void *)(new_cs), (void *)(ConsultSp), OldConsultCapacity*sizeof(consult_obj));
  /* copying done, release old space */
  FreeCodeSpace((char *)ConsultLow);
  /* next, set up pointers correctly */
  ConsultSp = new_cs;
  ConsultBase = new_cb;
  ConsultLow = new_cl;
}

/* p was already locked */
static int 
not_was_reconsulted(PredEntry *p, Term t, int mode)
{
  register consult_obj  *fp;
  Prop                   p0 = AbsProp((PropEntry *)p);

  for (fp = ConsultSp; fp < ConsultBase; ++fp)
    if (fp->p == p0)
      break;
  if (fp != ConsultBase)
    return (FALSE);
  if (mode) {
    if (ConsultSp == ConsultLow+1)
      expand_consult();
    --ConsultSp;
    ConsultSp->p = p0;
    if (ConsultBase[1].mode) /* we are in reconsult mode */ {
      if (static_in_use(p, TRUE)) {
	Int Arity = p->ArityOfPE;

	list_all_predicates_in_use();
	ErrorMessage = ErrorSay;
	Error_Term = t;
	Error_TYPE = PERMISSION_ERROR_MODIFY_STATIC_PROCEDURE;
	if (Arity == 0)
	  sprintf(ErrorMessage, "predicate %s is in use", RepAtom((Atom)(p->FunctorOfPred))->StrOfAE);
	else
	  sprintf(ErrorMessage,
#if SHORT_INTS
		  "predicate %s/%ld is in use",
#else
		  "predicate %s/%d is in use",
#endif
		  RepAtom(NameOfFunctor(p->FunctorOfPred))->StrOfAE, Arity);
	return(FALSE);
      }
      retract_all(p);
    }
    if (!(p->PredFlags & MultiFileFlag)) {
      p->OwnerFile = YapConsultingFile();
    }
  }
  return (TRUE);		/* careful */
}

static void
addcl_permission_error(AtomEntry *ap, Int Arity, int in_use) 
{
  Term t, ti[2];

  ti[0] = MkAtomTerm(AbsAtom(ap));
  ti[1] = MkIntegerTerm(Arity);
  t = MkApplTerm(MkFunctor(LookupAtom("/"),2), 2, ti);
  ErrorMessage = ErrorSay;
  Error_Term = t;
  Error_TYPE = PERMISSION_ERROR_MODIFY_STATIC_PROCEDURE;
  if (in_use) {
    if (Arity == 0)
      sprintf(ErrorMessage, "static predicate %s is in use", ap->StrOfAE);
    else
      sprintf(ErrorMessage,
#if SHORT_INTS
	      "static predicate %s/%ld is in use",
#else
	      "static predicate %s/%d is in use",
#endif
	      ap->StrOfAE, Arity);
  } else {
    if (Arity == 0)
      sprintf(ErrorMessage, "system predicate %s", ap->StrOfAE);
    else
      sprintf(ErrorMessage,
#if SHORT_INTS
	      "system predicate %s/%ld",
#else
	      "system predicate %s/%d",
#endif
	      ap->StrOfAE, Arity);
  }
}


void
addclause(Term t, CODEADDR cp, int mode, int mod)
/*
 * mode		0  assertz 1  consult 2  asserta				 
 */
{
  PredEntry      *p;
  int             spy_flag = FALSE;
  Atom           at;
  UInt           Arity;


  if (IsApplTerm(t) && FunctorOfTerm(t) == FunctorAssert)
    t = ArgOfTerm(1, t);
  if (IsAtomTerm(t)) {
    at = AtomOfTerm(t);
    p = RepPredProp(PredPropByAtom(at, mod));
    Arity = 0;
  } else {
    Functor f = FunctorOfTerm(t);
    Arity = ArityOfFunctor(f);
    at = NameOfFunctor(f);
    p = RepPredProp(PredPropByFunc(f, mod));
  }
  PutValue(AtomAbol, TermNil);
  WRITE_LOCK(p->PRWLock);
  /* we are redefining a prolog module predicate */
  if (p->ModuleOfPred == 0 && mod != 0) {
    WRITE_UNLOCK(p->PRWLock);
    addcl_permission_error(RepAtom(at), Arity, FALSE);
    return;
  }
  /* The only problem we have now is when we need to throw away
     Indexing blocks
  */
  if (p->PredFlags & IndexedPredFlag) {
    if (!RemoveIndexation(p)) {
      /* should never happen */
      WRITE_UNLOCK(p->PRWLock);
      addcl_permission_error(RepAtom(at),Arity,TRUE);
      return;
    }
  }
  if (p->PredFlags & SpiedPredFlag)
    spy_flag = TRUE;
  if (mode == consult)
    not_was_reconsulted(p, t, TRUE);
  if (!is_dynamic(p)) {
    Clause     *clp = ClauseCodeToClause(cp);
    clp->ClFlags |= StaticMask;
    if (compile_mode)
      p->PredFlags |= CompiledPredFlag | FastPredFlag;
    else
      p->PredFlags |= CompiledPredFlag;
    if ((GetValue(AtomIndex) != TermNil) && 
	(p->FirstClause != NIL) &&
	(Arity != 0)) {
      p->OpcodeOfPred = INDEX_OPCODE;
      p->CodeOfPred = (CODEADDR)(&(p->OpcodeOfPred)); 
    }
  }
  if (p->FirstClause == NIL) {
    if (!(p->PredFlags & DynamicPredFlag)) {
      add_first_static(p, cp, spy_flag);
      /* make sure we have a place to jump to */
      if (p->OpcodeOfPred == UNDEF_OPCODE) {
	p->CodeOfPred = p->TrueCodeOfPred;
	p->OpcodeOfPred = ((yamop *)(p->CodeOfPred))->opc;
      }
    } else {
      add_first_dynamic(p, cp, spy_flag);
    }
  } else if (mode == asserta) {
    if (p->PredFlags & DynamicPredFlag)
      asserta_dynam_clause(p, cp);
    else
      asserta_stat_clause(p, cp, spy_flag);
  } else if (p->PredFlags & DynamicPredFlag)
    assertz_dynam_clause(p, cp);
  else {
    assertz_stat_clause(p, cp, spy_flag);
    if (p->OpcodeOfPred != INDEX_OPCODE &&
	p->OpcodeOfPred != opcode(_spy_pred)) {
      p->CodeOfPred = p->TrueCodeOfPred;
      p->OpcodeOfPred = ((yamop *)(p->CodeOfPred))->opc;
    }
  }
  WRITE_UNLOCK(p->PRWLock);
}

static Int 
p_in_this_f_before(void)
{				/* '$in_this_file_before'(N,A,M) */
  unsigned int    arity;
  Atom            at;
  Term            t;
  register consult_obj  *fp;
  Prop            p0;
  SMALLUNSGN      mod;

  if (IsVarTerm(t = Deref(ARG1)) && !IsAtomTerm(t))
    return (FALSE);
  else
    at = AtomOfTerm(t);
  if (IsVarTerm(t = Deref(ARG2)) && !IsIntTerm(t))
    return (FALSE);
  else
    arity = IntOfTerm(t);
  if (IsVarTerm(t = Deref(ARG3)) && !IsAtomTerm(t))
    return (FALSE);
  else
    mod = LookupModule(t);
  if (arity)
    p0 = PredPropByFunc(MkFunctor(at, arity),CurrentModule);
  else
    p0 = PredPropByAtom(at, CurrentModule);
  if (ConsultSp == ConsultBase || (fp = ConsultSp)->p == p0)
    return (FALSE);
  else
    fp++;
  for (; fp < ConsultBase; ++fp)
    if (fp->p == p0)
      break;
  if (fp != ConsultBase)
    return (TRUE);
  else
    return (FALSE);
}

static Int 
p_first_cl_in_f(void)
{				/* '$first_cl_in_file'(+N,+Ar,+Mod) */
  unsigned int    arity;
  Atom            at;
  Term            t;
  register consult_obj  *fp;
  Prop            p0;
  SMALLUNSGN      mod;
  

  if (IsVarTerm(t = Deref(ARG1)) && !IsAtomTerm(t))
    return (FALSE);
  else
    at = AtomOfTerm(t);
  if (IsVarTerm(t = Deref(ARG2)) && !IsIntTerm(t))
    return (FALSE);
  else
    arity = IntOfTerm(t);
  if (IsVarTerm(t = Deref(ARG3)) && !IsAtomTerm(t))
    return (FALSE);
  else
    mod = LookupModule(t);
  if (arity)
    p0 = PredPropByFunc(MkFunctor(at, arity),mod);
  else
    p0 = PredPropByAtom(at, mod);
  for (fp = ConsultSp; fp < ConsultBase; ++fp)
    if (fp->p == p0)
      break;
  if (fp != ConsultBase)
    return (FALSE);
  return (TRUE);
}

static Int 
p_mk_cl_not_first(void)
{				/* '$mk_cl_not_first'(+N,+Ar) */
  unsigned int    arity;
  Atom            at;
  Term            t;
  Prop            p0;

  if (IsVarTerm(t = Deref(ARG1)) && !IsAtomTerm(t))
    return (FALSE);
  else
    at = AtomOfTerm(t);
  if (IsVarTerm(t = Deref(ARG2)) && !IsIntTerm(t))
    return (FALSE);
  else
    arity = IntOfTerm(t);
  if (arity)
    p0 = PredPropByFunc(MkFunctor(at, arity),CurrentModule);
  else
    p0 = PredPropByAtom(at, CurrentModule);
  --ConsultSp;
  ConsultSp->p = p0;
  return (TRUE);
}

#if EMACS
static int 
last_clause_number(p)
     PredEntry      *p;
{
  int             i = 1;
  CODEADDR        q = p->FirstClause;

  if (q == NIL)
    return (0);
  while (q != p->LastClause) {
    q = NextClause(q);
    i++;
  }
  return (i);
}


/*
 * the place where one would add a new clause for the propriety pred_prop 
 */
int 
where_new_clause(pred_prop, mode)
     Prop            pred_prop;
     int             mode;
{
  PredEntry      *p = RepPredProp(pred_prop);

  if (mode == consult && not_was_reconsulted(p, TermNil, FALSE))
    return (1);
  else
    return (last_clause_number(p) + 1);
}
#endif

static Int 
p_compile(void)
{				/* '$compile'(+C,+Flags, Mod) */
  Term            t = Deref(ARG1);
  Term            t1 = Deref(ARG2);
  Term            t3 = Deref(ARG3);
  CODEADDR        codeadr;
  Int mod;

  if (IsVarTerm(t1) || !IsIntTerm(t1))
    return (FALSE);
  if (IsVarTerm(t3) || !IsAtomTerm(t3))
    return (FALSE);
  mod = LookupModule(t3);
  codeadr = cclause(t, 2, mod); /* vsc: give the number of arguments
			      to cclause in case there is overflow */
  t = Deref(ARG1);        /* just in case there was an heap overflow */
  if (!ErrorMessage)
    addclause(t, codeadr, (int) (IntOfTerm(t1) & 3), mod);
  if (ErrorMessage) {
    if (IntOfTerm(t1) & 4) {
      Error(Error_TYPE, Error_Term,
	    "in line %d, %s", StartLine, ErrorMessage);
    } else
      Error(Error_TYPE, Error_Term, ErrorMessage);
    return (FALSE);
  }
  return (TRUE);
}

static Int 
p_compile_dynamic(void)
{				/* '$compile_dynamic'(+C,+Flags,Mod,-Ref) */
  Term            t = Deref(ARG1);
  Term            t1 = Deref(ARG2);
  Term            t3 = Deref(ARG3);
  Clause         *cl;
  CODEADDR        code_adr;
  int             old_optimize;
  Int mod;

  if (IsVarTerm(t1) || !IsIntTerm(t1))
    return (FALSE);
  if (IsVarTerm(t3) || !IsAtomTerm(t3))
    return (FALSE);
  old_optimize = optimizer_on;
  optimizer_on = FALSE;
  mod = LookupModule(t3);
  code_adr = cclause(t, 3, mod); /* vsc: give the number of arguments to
			       cclause() in case there is a overflow */
  t = Deref(ARG1);        /* just in case there was an heap overflow */
  if (!ErrorMessage) {
    
    optimizer_on = old_optimize;
    cl = ClauseCodeToClause(code_adr);
    addclause(t, code_adr, (int) (IntOfTerm(t1) & 3), mod);
  }
  if (ErrorMessage) {
    if (IntOfTerm(t1) & 4) {
      Error(Error_TYPE, Error_Term, "line %d, %s", StartLine, ErrorMessage);
    } else
      Error(Error_TYPE, Error_Term, ErrorMessage);
    return (FALSE);
  }
  cl = ClauseCodeToClause(code_adr);
  if (!(cl->ClFlags & LogUpdMask))
    cl->ClFlags = DynamicMask;
  t = MkIntegerTerm((Int)code_adr);
  return(unify(ARG4, t));
}



static int      consult_level = 0;

Atom
YapConsultingFile (void)
{
  if (consult_level == 0) {
    return(LookupAtom("user"));
  } else {
    return(LookupAtom(ConsultBase[2].filename));
  }
}

/* consult file *file*, *mode* may be one of either consult or reconsult */
void
init_consult(int mode, char *file)
{
  ConsultSp--;
  ConsultSp->filename = file;
  ConsultSp--;
  ConsultSp->mode = mode;
  ConsultSp--;
  ConsultSp->c = (ConsultBase-ConsultSp);
  ConsultBase = ConsultSp;
#if !defined(YAPOR) && !defined(SBA)
  /*  if (consult_level == 0)
      do_toggle_static_predicates_in_use(TRUE); */
#endif
  consult_level++;
}

static Int 
p_startconsult(void)
{				/* '$start_consult'(+Mode)	 */
  Term            t;
  char           *smode = RepAtom(AtomOfTerm(Deref(ARG1)))->StrOfAE;
  int             mode;
  
  mode = strcmp("consult",smode);
  init_consult(mode, RepAtom(AtomOfTerm(Deref(ARG2)))->StrOfAE);
  t = MkIntTerm(consult_level);
  return (unify_constant(ARG3, t));
}

static Int 
p_showconslultlev(void)
{
  Term            t;

  t = MkIntTerm(consult_level);
  return (unify_constant(ARG1, t));
}

void
end_consult(void)
{
#if defined(YAPOR) || defined(THREADS)
  consult_obj  *fp;

  /* force indexing for static and dynamic update predicates
     after consult and not when all hell may break loose ! */
  for (fp = ConsultSp; fp < ConsultBase; ++fp) {
    PredEntry *pred = RepPredProp(fp->p);
    WRITE_LOCK(pred->PRWLock);
    if (pred->OpcodeOfPred == INDEX_OPCODE) {
      IPred((CODEADDR)pred);
      /* IPred does the unlocking */
    } else {
      WRITE_UNLOCK(pred->PRWLock);
    }
  }
#endif
  ConsultSp = ConsultBase;
  ConsultBase = ConsultSp+ConsultSp->c;
  ConsultSp += 3;
  consult_level--;
#if !defined(YAPOR) && !defined(SBA)
  /*  if (consult_level == 0)
      do_toggle_static_predicates_in_use(FALSE);*/
#endif
}

static Int 
p_endconsult(void)
{				/* '$end_consult'		 */
  end_consult();
  return (TRUE);
}

static Int 
p_purge_clauses(void)
{				/* '$purge_clauses'(+Func) */
  PredEntry      *pred;
  Term            t = Deref(ARG1);
  Term            t2 = Deref(ARG2);
  CODEADDR        q, q1;
  int             mod;

  PutValue(AtomAbol, MkAtomTerm(AtomNil));
  if (IsVarTerm(t))
    return (FALSE);
  if (IsVarTerm(t2) || !IsAtomTerm(t2)) {
    return (FALSE);
  }
  mod = LookupModule(t2);
  if (IsAtomTerm(t)) {
    Atom at = AtomOfTerm(t);
    pred = RepPredProp(PredPropByAtom(at, mod));
  } else if (IsApplTerm(t)) {
    Functor         fun = FunctorOfTerm(t);
    pred = RepPredProp(PredPropByFunc(fun, mod));
  } else
    return (FALSE);
  WRITE_LOCK(pred->PRWLock);
  if (pred->PredFlags & StandardPredFlag) {
    WRITE_UNLOCK(pred->PRWLock);
    Error(PERMISSION_ERROR_MODIFY_STATIC_PROCEDURE, t, "assert/1");
    return (FALSE);
  }
  if (pred->PredFlags & IndexedPredFlag)
    RemoveIndexation(pred);
  PutValue(AtomAbol, MkAtomTerm(AtomTrue));
  q = pred->FirstClause;
  if (q != NIL)
    do {
      q1 = q;
      q = NextClause(q);
      if (pred->PredFlags & LogUpdatePredFlag)
	ErCl(ClauseCodeToClause(q1));
      else
	FreeCodeSpace((char *)ClauseCodeToClause(q1));
    } while (q1 != pred->LastClause);
  pred->FirstClause = pred->LastClause = NIL;
  pred->OpcodeOfPred = UNDEF_OPCODE;
  pred->TrueCodeOfPred =
    pred->CodeOfPred =
    (CODEADDR)(&(pred->OpcodeOfPred)); 
  pred->OwnerFile = AtomNil;
  if (pred->PredFlags & MultiFileFlag)
    pred->PredFlags ^= MultiFileFlag;
  WRITE_UNLOCK(pred->PRWLock);
  return (TRUE);
}

/******************************************************************
  
		MANAGING SPY-POINTS
  
******************************************************************/

static Int 
p_setspy(void)
{				/* '$set_spy'(+Fun,+M)	 */
  Atom            at;
  PredEntry      *pred;
  CELL            fg;
  Term            t;
  Term            t2;
  SMALLUNSGN	  mod;

  at = FullLookupAtom("$spy");
  pred = RepPredProp(PredPropByFunc(MkFunctor(at, 1),0));
  SpyCode = pred;
  t = Deref(ARG1);
  t2 = Deref(ARG2);
  if (IsVarTerm(t))
    return (FALSE);
  if (IsVarTerm(t2) || !IsAtomTerm(t2))
    return (FALSE);
  mod = LookupModule(t2);
  if (IsAtomTerm(t)) {
    Atom at = AtomOfTerm(t);
    pred = RepPredProp(PredPropByAtom(at, mod));
  } else if (IsApplTerm(t)) {
    Functor fun = FunctorOfTerm(t);
    pred = RepPredProp(PredPropByFunc(fun, mod));
  } else {
    return (FALSE);
  }
 restart_spy:
  WRITE_LOCK(pred->PRWLock);
  if (pred->PredFlags & (CPredFlag | SafePredFlag)) {
    WRITE_UNLOCK(pred->PRWLock);
    return (FALSE);
  }
  if (pred->OpcodeOfPred == UNDEF_OPCODE) {
    WRITE_UNLOCK(pred->PRWLock);
    return (FALSE);
  }
  if (pred->OpcodeOfPred == INDEX_OPCODE) {
    IPred((CODEADDR)pred);
    goto restart_spy;
  }
  fg = pred->PredFlags;
  if (fg & DynamicPredFlag) {
    pred->OpcodeOfPred =
      ((yamop *)(pred->CodeOfPred))->opc =
      opcode(_spy_or_trymark);
  } else {
    pred->OpcodeOfPred = opcode(_spy_pred);
    pred->CodeOfPred = (CODEADDR)(&(pred->OpcodeOfPred)); 
  }
  pred->StateOfPred |= SpiedMask;
  pred->PredFlags |= SpiedPredFlag;
  WRITE_UNLOCK(pred->PRWLock);
  return (TRUE);
}

static Int 
p_rmspy(void)
{				/* '$rm_spy'(+T,+Mod)	 */
  Atom            at;
  PredEntry      *pred;
  Term            t;
  Term            t2;
  SMALLUNSGN	  mod;

  t = Deref(ARG1);
  t2 = Deref(ARG2);
  if (IsVarTerm(t2) || !IsAtomTerm(t2))
    return (FALSE);
  mod = LookupModule(t2);
  if (IsVarTerm(t))
    return (FALSE);
  if (IsAtomTerm(t)) {
    at = AtomOfTerm(t);
    pred = RepPredProp(PredPropByAtom(at, mod));
  } else if (IsApplTerm(t)) {
    Functor fun = FunctorOfTerm(t);
    pred = RepPredProp(PredPropByFunc(fun, mod));
  } else
    return (FALSE);
  WRITE_LOCK(pred->PRWLock);
  if (!(pred->PredFlags & SpiedPredFlag)) {
    WRITE_UNLOCK(pred->PRWLock);
    return (FALSE);
  }
  if (!(pred->PredFlags & DynamicPredFlag)) {
    if ((pred->StateOfPred ^= SpiedMask) & InUseMask)
      pred->CodeOfPred = pred->TrueCodeOfPred;
    else
      pred->CodeOfPred = pred->TrueCodeOfPred;
    pred->OpcodeOfPred = ((yamop *)(pred->CodeOfPred))->opc;
  } else if (pred->OpcodeOfPred == opcode(_spy_or_trymark)) {
    pred->OpcodeOfPred = opcode(_try_and_mark);
  } else
    return (FALSE);
  pred->PredFlags ^= SpiedPredFlag;
  WRITE_UNLOCK(pred->PRWLock);
  return (TRUE);
}


/******************************************************************
  
		INFO ABOUT PREDICATES
  
******************************************************************/

static Int 
p_number_of_clauses(void)
{				/* '$number_of_clauses'(Predicate,M,N) */
  Term            t = Deref(ARG1);
  Term            t2 = Deref(ARG2);
  int ncl = 0;
  Prop            pe;
  CODEADDR        q;
  int             testing;
  int             mod;

  if (IsVarTerm(t2)  || !IsAtomTerm(t2)) {
    return(FALSE);
  }
  mod = LookupModule(t2);
  if (IsAtomTerm(t)) {
    Atom a = AtomOfTerm(t);
    pe = PredPropByAtom(a, mod);
  } else if (IsApplTerm(t)) {
    register Functor f = FunctorOfTerm(t);
    pe = PredPropByFunc(f, mod);
  } else
    return (FALSE);
  q = RepPredProp(pe)->FirstClause;
  READ_LOCK(RepPredProp(pe)->PRWLock);
  if (q != NIL) {
    if (RepPredProp(pe)->PredFlags & DynamicPredFlag)
      testing = TRUE;
    else
      testing = FALSE;
    while (q != RepPredProp(pe)->LastClause) {
      if (!testing ||
	  !(ClauseCodeToClause(q)->ClFlags & ErasedMask))
	ncl++;
      q = NextClause(q);
    }
    if (!testing ||
	!(ClauseCodeToClause(q)->ClFlags & ErasedMask))
      ncl++;
  }
  READ_UNLOCK(RepPredProp(pe)->PRWLock);
  t = MkIntTerm(ncl);
  return (unify_constant(ARG3, t));
}

static Int 
p_in_use(void)
{				/* '$in_use'(+P,+Mod)	 */
  Term            t = Deref(ARG1);
  Term            t2 = Deref(ARG2);
  PredEntry      *pe;
  Int            out;
  int            mod;

  if (IsVarTerm(t))
    return (FALSE);
  if (IsVarTerm(t2) || !IsAtomTerm(t2))
    return (FALSE);
  mod = LookupModule(t2);
  if (IsAtomTerm(t)) {
    Atom at = AtomOfTerm(t);
    pe = RepPredProp(PredPropByAtom(at, mod));
  } else if (IsApplTerm(t)) {
    Functor         fun = FunctorOfTerm(t);
    pe = RepPredProp(PredPropByFunc(fun, mod));
  } else
    return (FALSE);
  READ_LOCK(pe->PRWLock);
  out = static_in_use(pe,TRUE);
  READ_UNLOCK(pe->PRWLock);
  return(out);
}

static Int 
p_new_multifile(void)
{				/* '$new_multifile'(+N,+Ar,+Mod)  */
  Atom            at;
  int             arity;
  PredEntry      *pe;
  Term            t = Deref(ARG1);
  SMALLUNSGN      mod = LookupModule(Deref(ARG3));

  if (IsVarTerm(t))
    return (FALSE);
  if (IsAtomTerm(t))
    at = AtomOfTerm(t);
  else
    return (FALSE);
  t = Deref(ARG2);
  if (IsVarTerm(t))
    return (FALSE);
  if (IsIntTerm(t))
    arity = IntOfTerm(t);
  else
    return (FALSE);
  if (arity == 0) 
    pe = RepPredProp(PredPropByAtom(at, mod));
  else 
    pe = RepPredProp(PredPropByFunc(MkFunctor(at, arity),mod));
  WRITE_LOCK(pe->PRWLock);
  pe->PredFlags |= MultiFileFlag;
  WRITE_UNLOCK(pe->PRWLock);
  return (TRUE);
}


static Int 
p_is_multifile(void)
{				/* '$is_multifile'(+S,+Mod)	 */
  PredEntry      *pe;
  Term            t = Deref(ARG1);
  Term            t2 = Deref(ARG2);
  Int		  out;
  int		  mod;

  if (IsVarTerm(t))
    return (FALSE);
  if (IsVarTerm(t2))
    return (FALSE);
  if (!IsAtomTerm(t2))
    return (FALSE);
  mod = LookupModule(t2);
  if (IsAtomTerm(t)) {
    pe = RepPredProp(PredPropByAtom(AtomOfTerm(t), mod));
  } else if (IsApplTerm(t)) {
    pe = RepPredProp(PredPropByFunc(FunctorOfTerm(t), mod));
  } else
    return(FALSE);
  if (EndOfPAEntr(pe))
    return (FALSE);
  READ_LOCK(pe->PRWLock);
  out = (pe->PredFlags & MultiFileFlag);
  READ_UNLOCK(pe->PRWLock);
  return(out);
}

static Int 
p_is_dynamic(void)
{				/* '$is_dynamic'(+P)	 */
  PredEntry      *pe;
  Term            t = Deref(ARG1);
  Term            t2 = Deref(ARG2);
  Int             out;
  SMALLUNSGN      mod = LookupModule(t2);

  if (IsVarTerm(t)) {
    return (FALSE);
  } else if (IsAtomTerm(t)) {
    Atom at = AtomOfTerm(t);
    pe = RepPredProp(PredPropByAtom(at, mod));
  } else if (IsApplTerm(t)) {
    Functor         fun = FunctorOfTerm(t);
    pe = RepPredProp(PredPropByFunc(fun, mod));
  } else
    return (FALSE);
  if (pe == NIL)
    return (FALSE);
  READ_LOCK(pe->PRWLock);
  out = (pe->PredFlags & (DynamicPredFlag|LogUpdatePredFlag));
  READ_UNLOCK(pe->PRWLock);
  return(out);
}

static Int 
p_set_pred_module(void)
{				/* '$set_pred_module'(+P,+Mod)	 */
  PredEntry      *pe;
  Term            t = Deref(ARG1);
  SMALLUNSGN      mod = CurrentModule;

 restart_set_pred:
  if (IsVarTerm(t)) {
    return (FALSE);
  } else if (IsAtomTerm(t)) {
    pe = RepPredProp(PredPropByAtom(AtomOfTerm(t), mod));
  } else if (IsApplTerm(t)) {
    Functor         fun = FunctorOfTerm(t);
    if (fun == FunctorModule) {
      Term tmod = ArgOfTerm(1, t);
      if (IsVarTerm(tmod) ) {
	Error(INSTANTIATION_ERROR,ARG1,"set_pred_module/1");
	return(FALSE);
      }
      if (!IsAtomTerm(tmod) ) {
	Error(TYPE_ERROR_ATOM,ARG1,"set_pred_module/1");
	return(FALSE);
      }
      mod = LookupModule(tmod);
      t = ArgOfTerm(2, t);
      goto restart_set_pred;
    }
    pe = RepPredProp(PredPropByFunc(fun, mod));
  } else
    return (FALSE);
  if (EndOfPAEntr(pe))
    return (FALSE);
  WRITE_LOCK(pe->PRWLock);
  {
    SMALLUNSGN mod = LookupModule(Deref(ARG2));
    pe->ModuleOfPred = mod;
  }
  WRITE_UNLOCK(pe->PRWLock);
  return(TRUE);
}

static Int 
p_undefined(void)
{				/* '$undefined'(P,Mod)	 */
  PredEntry      *pe;
  Term            t;
  Term            t2;
  SMALLUNSGN      mod;

  t = Deref(ARG1);
  t2 = Deref(ARG2);
  if (IsVarTerm(t2)) {
    Error(INSTANTIATION_ERROR,ARG2,"undefined/1");
    return(FALSE);
  }
  if (!IsAtomTerm(t2)) {
    Error(TYPE_ERROR_ATOM,ARG2,"undefined/1");
    return(FALSE);
  }
  mod = LookupModule(t2);
 restart_undefined:
  if (IsVarTerm(t)) {
    Error(INSTANTIATION_ERROR,ARG1,"undefined/1");
    return(FALSE);
  }
  if (IsAtomTerm(t)) {
    Atom at = AtomOfTerm(t);
    pe = RepPredProp(GetPredPropByAtom(at,mod));
  } else if (IsApplTerm(t)) {
    Functor         funt = FunctorOfTerm(t);
    if (funt == FunctorModule) {
      Term tmod = ArgOfTerm(1, t);
      if (IsVarTerm(tmod) ) {
	Error(INSTANTIATION_ERROR,ARG1,"undefined/1");
	return(FALSE);
      }
      if (!IsAtomTerm(tmod) ) {
	Error(TYPE_ERROR_ATOM,ARG1,"undefined/1");
	return(FALSE);
      }
      mod = LookupModule(tmod);
      t = ArgOfTerm(2, t);
      goto restart_undefined;
    }
    pe = RepPredProp(GetPredPropByFunc(funt, mod));
  } else {
    return (FALSE);
  }
  if (pe == RepPredProp(NIL))
    return (TRUE);
  READ_LOCK(pe->PRWLock);
  if (pe->PredFlags & (CPredFlag|UserCPredFlag|TestPredFlag|BasicPredFlag|DynamicPredFlag)) {
    READ_UNLOCK(pe->PRWLock);
    return(FALSE);
  }
  if (pe->OpcodeOfPred == UNDEF_OPCODE) {
    READ_UNLOCK(pe->PRWLock);
    return (TRUE);
  }
  READ_UNLOCK(pe->PRWLock);
  return (FALSE);
}

/*
 * this predicate should only be called when all clauses for the dynamic
 * predicate were remove, otherwise chaos will follow!! 
 */

static Int 
p_kill_dynamic(void)
{				/* '$kill_dynamic'(P,M)       */
  PredEntry      *pe;
  Term            t;
  Term            t2;
  SMALLUNSGN      mod;

  t2 = Deref(ARG2);
  if (IsVarTerm(t2)) {
    Error(INSTANTIATION_ERROR,ARG2,"undefined/1");
    return(FALSE);
  }
  if (!IsAtomTerm(t2)) {
    Error(TYPE_ERROR_ATOM,ARG2,"undefined/1");
    return(FALSE);
  }
  mod = LookupModule(t2);
  t = Deref(ARG1);
  if (IsAtomTerm(t)) {
    Atom at = AtomOfTerm(t);
    pe = RepPredProp(PredPropByAtom(at, mod));
  } else if (IsApplTerm(t)) {
    Functor         funt = FunctorOfTerm(t);
    pe = RepPredProp(PredPropByFunc(funt, mod));
  } else
    return (FALSE);
  if (EndOfPAEntr(pe))
    return (TRUE);
  WRITE_LOCK(pe->PRWLock);
  if (!(pe->PredFlags & DynamicPredFlag)) {
    WRITE_UNLOCK(pe->PRWLock);
    return (FALSE);
  }
  if (pe->LastClause != pe->FirstClause) {
    WRITE_UNLOCK(pe->PRWLock);
    return (FALSE);
  }
  pe->LastClause = pe->FirstClause = NIL;
  pe->OpcodeOfPred = UNDEF_OPCODE;
  pe->TrueCodeOfPred = pe->CodeOfPred = (CODEADDR)(&(pe->OpcodeOfPred)); 
  pe->PredFlags = 0L;
  WRITE_UNLOCK(pe->PRWLock);
  return (TRUE);
}

static Int 
p_optimizer_on(void)
{				/* '$optimizer_on'		 */
  optimizer_on = TRUE;
  return (TRUE);
}

static Int 
p_optimizer_off(void)
{				/* '$optimizer_off'		 */
  optimizer_on = FALSE;
  return (TRUE);
}

static Int 
p_compile_mode(void)
{				/* $compile_mode(Old,New)	 */
  Term            t2, t3 = MkIntTerm(compile_mode);
  if (!unify_constant(ARG1, t3))
    return (FALSE);
  t2 = Deref(ARG2);
  if (IsVarTerm(t2) || !IsIntTerm(t2))
    return (FALSE);
  compile_mode = IntOfTerm(t2) & 1;
  return (TRUE);
}

#if !defined(YAPOR) && !defined(THREADS)
static Int
search_for_static_predicate_in_use(PredEntry *p, int check_everything)
{
  choiceptr b_ptr = B;
  CELL *env_ptr = ENV;

  do {
    /* check first environments that are younger than our latest choicepoint */
    if (check_everything) {
      /* 
	 I do not need to check environments for asserts,
	 only for retracts
      */
      while (b_ptr > (choiceptr)env_ptr) {
	PredEntry *pe = EnvPreg(env_ptr[E_CP]);
	if (p == pe) return(TRUE);
	if (env_ptr != NULL)
	  env_ptr = (CELL *)(env_ptr[E_E]);
      }
    }
    /* now mark the choicepoint */
    if (b_ptr != NULL) {
      PredEntry *pe;
      op_numbers opnum = op_from_opcode(b_ptr->cp_ap->opc);
      
    restart_cp:
      switch(opnum) {
      case _or_else:
      case _or_last:
	if (!check_everything) {
	  b_ptr = b_ptr->cp_b;
	  continue;
	}
#ifdef YAPOR
	pe = b_ptr->cp_cp->u.ldl.p;
#else
	pe = b_ptr->cp_cp->u.sla.p0;
#endif /* YAPOR */
	break;
      case _retry_profiled:
	opnum = op_from_opcode(NEXTOP(b_ptr->cp_ap,l)->opc);
	goto restart_cp;
      default:
	pe = (PredEntry *)(b_ptr->cp_ap->u.ld.p);
      }
      if (pe == p) {
	if (check_everything) return(TRUE);
	READ_LOCK(pe->PRWLock);
	if (p->PredFlags & IndexedPredFlag) {
	  CODEADDR code_p = (CODEADDR)(b_ptr->cp_ap);
	  if (code_p >= p->TrueCodeOfPred &&
	      code_p <= p->TrueCodeOfPred + SizeOfBlock(p->TrueCodeOfPred)) {
	    /* oops, we are trying to assert a clause and we have a pointer
	       to its indexing code live in the local stack */
	    READ_UNLOCK(pe->PRWLock);
	    return(TRUE);
	  }
	}
	READ_UNLOCK(pe->PRWLock);
      }
      env_ptr = b_ptr->cp_env;
      b_ptr = b_ptr->cp_b;
    }
  } while (b_ptr != NULL);
  return(FALSE);
}

#ifdef DEBUG
#ifndef ANALYST

static char *op_names[_std_top + 1] =
{
#define OPCODE(OP,TYPE) #OP
#include "YapOpcodes.h"
#undef  OPCODE
};

#endif


static void
list_all_predicates_in_use(void)
{
  choiceptr b_ptr = B;
  CELL *env_ptr = ENV;

  do {
      /* 
	 I do not need to check environments for asserts,
	 only for retracts
      */
    while (b_ptr > (choiceptr)env_ptr) {
      PredEntry *pe = EnvPreg(env_ptr[E_CP]);
      op_numbers op = op_from_opcode(ENV_ToOp(env_ptr[E_CP]));
      if (pe->ArityOfPE)
	YP_fprintf(YP_stderr,"   ENV %p  %s/%d %s\n", env_ptr, RepAtom(NameOfFunctor(pe->FunctorOfPred))->StrOfAE, pe->ArityOfPE, op_names[op]);
      else
	YP_fprintf(YP_stderr,"   ENV %p  %s %s\n", env_ptr, RepAtom((Atom)(pe->FunctorOfPred))->StrOfAE, op_names[op]);
      env_ptr = (CELL *)(env_ptr[E_E]);      
    }
  restart_cp:
    /* now mark the choicepoint */
    if (b_ptr != NULL) {
      op_numbers opnum = op_from_opcode(b_ptr->cp_ap->opc);
      
      switch (opnum) {
      case _or_else:
      case _or_last:
      case _Nstop:
      case _switch_last:
      case _switch_l_list:
      case _retry_c:
      case _retry_userc:
      case _trust_logical_pred:
      case _retry_profiled:
	{
	  Atom at;
	  Int arity;
	  SMALLUNSGN mod;
	  if (PredForCode((CODEADDR)b_ptr->cp_ap, &at, &arity, &mod)) {
	    if (arity) 
	      YP_fprintf(YP_stderr,"CP  %p  %s/%d (%s)\n", b_ptr, RepAtom(at)->StrOfAE, arity, op_names[opnum]);
	    else
	      YP_fprintf(YP_stderr,"CP  %p  %s (%s)\n", b_ptr, RepAtom(at)->StrOfAE, op_names[opnum]);
	  } else
	    YP_fprintf(YP_stderr,"CP  %p  (%s)\n", op_names[opnum], b_ptr);
	}
	break;
      default:
	{
	  PredEntry *pe = (PredEntry *)b_ptr->cp_ap->u.ld.p;
	  if (pe == NULL) {
	    YP_fprintf(YP_stderr,"CP  %p  (%s)\n", b_ptr, op_names[opnum]);
	  } else
	    if (pe->ArityOfPE)
	      YP_fprintf(YP_stderr,"CP  %p  %s/%d (%s)\n", b_ptr, RepAtom(NameOfFunctor(pe->FunctorOfPred))->StrOfAE, pe->ArityOfPE, op_names[opnum]);
	    else
	      YP_fprintf(YP_stderr,"CP  %p  %d (%s)\n", b_ptr, RepAtom((Atom)(pe->FunctorOfPred))->StrOfAE, op_names[opnum]);
	}
      }
      if (opnum == _retry_profiled) {
	opnum = op_from_opcode(NEXTOP(b_ptr->cp_ap,l)->opc);
	goto restart_cp;
      }
    }
    env_ptr = b_ptr->cp_env;
    b_ptr = b_ptr->cp_b;
  } while (b_ptr != NULL);
}
#endif

static void
mark_pred(int mark, PredEntry *pe)
{
  /* if the predicate is static mark it */
  if (pe->ModuleOfPred) {
    WRITE_LOCK(pe->PRWLock);
    if (mark) {
      pe->StateOfPred |= InUseMask;
    } else {
      pe->StateOfPred &= ~InUseMask;
    }
    WRITE_UNLOCK(pe->PRWLock);
  }
}

/* go up the chain of choice_points and environments,
   marking all static predicates that current execution is depending 
   upon */
static void
do_toggle_static_predicates_in_use(int mask)
{
  choiceptr b_ptr = B;
  CELL *env_ptr = ENV;

  if (b_ptr == NULL)
    return;

  do {
    PredEntry *pe;
    /* check first environments that are younger than our latest choicepoint */
    while (b_ptr > (choiceptr)env_ptr) {
      PredEntry *pe = EnvPreg(env_ptr[E_CP]);
      
<<<<<<< cdmgr.c
      mark_pred(mask, pe);
=======
      if (pe != NULL && FALSE) {
	op_numbers op = op_from_opcode(ENV_ToOp(env_ptr[E_CP]));
	if (pe->ArityOfPE)
	  YP_fprintf(YP_stderr,"ENV %p  %s/%d %s\n", env_ptr, RepAtom(NameOfFunctor(pe->FunctorOfPred))->StrOfAE, pe->ArityOfPE, op_names[op]);
	else
	  YP_fprintf(YP_stderr,"ENV %p  %s %s\n", env_ptr, RepAtom((Atom)(pe->FunctorOfPred))->StrOfAE, op_names[op]);
	if (env_ptr == 0x21d0b24) {
	  CELL *next_ee = (CELL *)(env_ptr[E_E]);
	  do {
	    YP_fprintf(YP_stderr,"looking for parent %p with CP %x value %x\n", next_ee, next_ee[E_CP], EnvPreg(next_ee[E_CP]));
	    next_ee = (CELL *)(next_ee[E_E]);
	   } while (next_ee != 0x21d0f28);
	}

	mark_pred(mask, pe);
      }
>>>>>>> 1.22
      env_ptr = (CELL *)(env_ptr[E_E]);
    }
    /* now mark the choicepoint */
    {
      op_numbers opnum;
    restart_cp:
      opnum = op_from_opcode(b_ptr->cp_ap->opc);
      
      switch(opnum) {
      case _or_else:
      case _or_last:
#ifdef YAPOR
	pe = b_ptr->cp_cp->u.ldl.p;
#else
	pe = b_ptr->cp_cp->u.sla.p0;
#endif /* YAPOR */
	break;
      case _Nstop:
	pe = NULL;
	break;
      case _retry_profiled:
	opnum = op_from_opcode(NEXTOP(b_ptr->cp_ap,l)->opc);
	goto restart_cp;
      default:
	pe = (PredEntry *)(b_ptr->cp_ap->u.ld.p);
      }
      if (pe != NULL)
	mark_pred(mask, pe);
      env_ptr = b_ptr->cp_env;
      b_ptr = b_ptr->cp_b;
    }
  } while (b_ptr != NULL);
  /* mark or unmark all predicates */
  STATIC_PREDICATES_MARKED = mask;
}

#endif

/* This predicate is to be used by reconsult to mark all predicates
   currently in use as being executed.

   The idea is to go up the chain of choice_points and environments.

 */
static Int
p_toggle_static_predicates_in_use(void)
{
#if !defined(YAPOR) && !defined(THREADS)
  Term t = Deref(ARG1);
  Int mask;
  
  /* find out whether we need to mark or unmark */
  if (IsVarTerm(t)) {
    Error(INSTANTIATION_ERROR,t,"toggle_static_predicates_in_use/1");
    return(FALSE);
  }
  if (!IsIntTerm(t)) {
    Error(TYPE_ERROR_INTEGER,t,"toggle_static_predicates_in_use/1");
    return(FALSE);
  }  else {
    mask = IntOfTerm(t);
  }
  do_toggle_static_predicates_in_use(mask);
#endif
  return(TRUE);
}


static Int
code_in_pred(PredEntry *pp, Atom *pat, Int *parity, CODEADDR codeptr) {
  CODEADDR clcode, cl;
  int i = 1;

  READ_LOCK(pp->PRWLock);
  clcode = pp->FirstClause;
  if (clcode != NIL) {
    /* check if the codeptr comes from the indexing code */
    if ((pp->PredFlags & IndexedPredFlag) &&
	codeptr > pp->TrueCodeOfPred &&
	codeptr <= pp->TrueCodeOfPred + SizeOfBlock(pp->TrueCodeOfPred)) {
      *parity = pp->ArityOfPE;
      if (pp->ArityOfPE) {
	*pat = NameOfFunctor(pp->FunctorOfPred);
      } else {
	*pat = (Atom)(pp->FunctorOfPred);
      }
      READ_UNLOCK(pp->PRWLock);
      return(-1);
    }	      
    cl = (CODEADDR)ClauseCodeToClause(clcode);
    do {
      if (codeptr > cl && codeptr <= cl + SizeOfBlock(cl)) {
	/* we found it */
	*parity = pp->ArityOfPE;
	if (pp->ArityOfPE) {
	  *pat = NameOfFunctor(pp->FunctorOfPred);
	} else {
	  *pat = (Atom)(pp->FunctorOfPred);
	}
	READ_UNLOCK(pp->PRWLock);
	return(i);
      }
      if (clcode == pp->LastClause)
	break;
      cl = (CODEADDR)ClauseCodeToClause(clcode = NextClause(clcode));
      i++;
    } while (TRUE);
  }
  READ_UNLOCK(pp->PRWLock); 
  return(0);
}

Int
PredForCode(CODEADDR codeptr, Atom *pat, Int *parity, SMALLUNSGN *pmodule) {
  Int found = 0;
  Int i_table;

  /* should we allow the user to see hidden predicates? */
  for (i_table = NoOfModules-1; i_table >= 0; --i_table) {
    PredEntry *pp = ModulePred[i_table];
    while (pp != NULL) {
      if ((found = code_in_pred(pp,  pat, parity, codeptr)) != 0) {
	*pmodule = i_table;
	return(found);
      }
      pp = pp->NextPredOfModule;
    }
  }
  return(0);
}

static Int
p_is_profiled(void)
{
  Term t = Deref(ARG1);
  char *s;

  if (IsVarTerm(t)) {
    Term ta;

    if (PROFILING) ta = MkAtomTerm(LookupAtom("on"));
    else ta = MkAtomTerm(LookupAtom("off"));
    BIND((CELL *)t,ta,bind_is_profiled);
#ifdef COROUTINING
    DO_TRAIL(CellPtr(t), ta);
    if (CellPtr(t) < H0) WakeUp((CELL *)t);
  bind_is_profiled:
#endif
    return(TRUE);
  } else if (!IsAtomTerm(t)) return(FALSE);
  s = RepAtom(AtomOfTerm(t))->StrOfAE;
  if (strcmp(s,"on") == 0) {
    PROFILING = TRUE;
    return(TRUE);
  } else if (strcmp(s,"off") == 0) {
    PROFILING = FALSE;
    return(TRUE);
  }
  return(FALSE);
}

static Int
p_profile_info(void)
{
  Term tmod = Deref(ARG1);
  Term tfun = Deref(ARG2);
  int mod;
  Term out;
  PredEntry *pe;
  Term p[3];

  if (IsVarTerm(tmod) || !IsAtomTerm(tmod))
    return(FALSE);
  mod = LookupModule(tmod);
  if (IsVarTerm(tfun)) {
    return(FALSE);
  } else if (IsApplTerm(tfun)) {
    Functor f = FunctorOfTerm(tfun);
    if (IsExtensionFunctor(f)) {
      return(FALSE);
    }
    pe = RepPredProp(GetPredPropByFunc(f, mod));
  } else if (IsAtomTerm(tfun)) {
    pe = RepPredProp(GetPredPropByAtom(AtomOfTerm(tfun), mod));
  } else {
    return(FALSE);
  }
  if (EndOfPAEntr(pe))
    return(FALSE);
  LOCK(pe->StatisticsForPred.lock);
  if (!(pe->StatisticsForPred.NOfEntries)) {
    UNLOCK(pe->StatisticsForPred.lock);
    return(FALSE);
  }
  p[0] = MkIntegerTerm(pe->StatisticsForPred.NOfEntries);
  p[1] = MkIntegerTerm(pe->StatisticsForPred.NOfHeadSuccesses);
  p[2] = MkIntegerTerm(pe->StatisticsForPred.NOfRetries);
  UNLOCK(pe->StatisticsForPred.lock);
  out = MkApplTerm(MkFunctor(AtomProfile,3),3,p);
  return(unify(ARG3,out));
}

static Int
p_profile_reset(void)
{
  Term tmod = Deref(ARG1);
  Term tfun = Deref(ARG2);
  int mod;
  PredEntry *pe;

  if (IsVarTerm(tmod) || !IsAtomTerm(tmod))
    return(FALSE);
  mod = LookupModule(tmod);
  if (IsVarTerm(tfun)) {
    return(FALSE);
  } else if (IsApplTerm(tfun)) {
    Functor f = FunctorOfTerm(tfun);
    if (IsExtensionFunctor(f)) {
      return(FALSE);
    }
    pe = RepPredProp(GetPredPropByFunc(f, mod));
  } else if (IsAtomTerm(tfun)) {
    pe = RepPredProp(GetPredPropByAtom(AtomOfTerm(tfun), mod));
  } else {
    return(FALSE);
  }
  if (EndOfPAEntr(pe))
    return(FALSE);
  LOCK(pe->StatisticsForPred.lock);
  pe->StatisticsForPred.NOfEntries = 0;
  pe->StatisticsForPred.NOfHeadSuccesses = 0;
  pe->StatisticsForPred.NOfRetries = 0;
  UNLOCK(pe->StatisticsForPred.lock);
  return(TRUE);
}

static Int
p_clean_up_dead_clauses(void)
{
  while (DeadClauses != NULL) {
    char *pt = (char *)DeadClauses;
    DeadClauses = DeadClauses->u.NextCl;
    FreeCodeSpace(pt);
  }
  return(TRUE);
}

static Int			/* $parent_pred(Module, Name, Arity) */
p_parent_pred(void)
{
  /* This predicate is called from the debugger.
     We assume a sequence of the form a -> b */
  Atom at;
  Int arity;
  SMALLUNSGN module;
  if (!PredForCode((CODEADDR)P_before_spy, &at, &arity, &module)) {
    return(unify(ARG1, MkIntTerm(0)) &&
	   unify(ARG2, MkAtomTerm(AtomMetaCall)) &&
	   unify(ARG3, MkIntTerm(0)));
  }
  return(unify(ARG1, MkIntTerm(module)) &&
	 unify(ARG2, MkAtomTerm(at)) &&
	 unify(ARG3, MkIntTerm(arity)));
}

static Int			/* $system_predicate(P) */
p_system_pred(void)
{
  PredEntry      *pe;

  Term t1 = Deref(ARG1);
  SMALLUNSGN mod = LookupModule(Deref(ARG2));

 restart_system_pred:
  if (IsVarTerm(t1))
    return (FALSE);
  if (IsAtomTerm(t1)) {
    pe = RepPredProp(GetPredPropByAtom(AtomOfTerm(t1), mod));
  } else if (IsApplTerm(t1)) {
    Functor         funt = FunctorOfTerm(t1);
    if (IsExtensionFunctor(funt)) {
      return(FALSE);
    } 
    if (funt == FunctorModule) {
      Term nmod = ArgOfTerm(1, t1);
      if (IsVarTerm(nmod)) {
	Error(INSTANTIATION_ERROR,ARG1,"system_predicate/1");
	return(FALSE);
      } 
      if (!IsAtomTerm(nmod)) {
	Error(TYPE_ERROR_ATOM,ARG1,"system_predicate/1");
	return(FALSE);
      }
      t1 = ArgOfTerm(2, t1);
      goto restart_system_pred;
    }
    pe = RepPredProp(GetPredPropByFunc(funt, mod));
  } else
    return (FALSE);
  if (EndOfPAEntr(pe))
    return(FALSE);
  return(pe->ModuleOfPred == 0 || pe->PredFlags & (UserCPredFlag|CPredFlag|BinaryTestPredFlag|BasicPredFlag|TestPredFlag));
}

static Int			/* $cut_transparent(P) */
p_cut_transparent(void)
{
  PredEntry      *pe;

  Term t1 = Deref(ARG1);
 restart_system_pred:
  if (IsVarTerm(t1))
    return (FALSE);
  if (IsAtomTerm(t1)) {
    pe = RepPredProp(GetPredPropByAtom(AtomOfTerm(t1), 0));
  } else if (IsApplTerm(t1)) {
    Functor         funt = FunctorOfTerm(t1);
    if (IsExtensionFunctor(funt)) {
      return(FALSE);
    } 
    if (funt == FunctorModule) {
      Term nmod = ArgOfTerm(1, t1);
      if (IsVarTerm(nmod)) {
	Error(INSTANTIATION_ERROR,ARG1,"system_predicate/1");
	return(FALSE);
      } 
      if (!IsAtomTerm(nmod)) {
	Error(TYPE_ERROR_ATOM,ARG1,"system_predicate/1");
	return(FALSE);
      }
      t1 = ArgOfTerm(2, t1);
      goto restart_system_pred;
    }
    pe = RepPredProp(GetPredPropByFunc(funt, 0));
  } else
    return (FALSE);
  if (EndOfPAEntr(pe))
    return(FALSE);
  pe->PredFlags |= CutTransparentPredFlag;
  return(TRUE);
}

void 
InitCdMgr(void)
{
  InitCPred("$compile_mode", 2, p_compile_mode, SafePredFlag|SyncPredFlag);
  InitCPred("$start_consult", 3, p_startconsult, SafePredFlag|SyncPredFlag);
  InitCPred("$show_consult_level", 1, p_showconslultlev, SafePredFlag);
  InitCPred("$end_consult", 0, p_endconsult, SafePredFlag|SyncPredFlag);
  InitCPred("$set_spy", 2, p_setspy, SafePredFlag|SyncPredFlag);
  InitCPred("$rm_spy", 2, p_rmspy, SafePredFlag|SyncPredFlag);
  /* gc() may happen during compilation, hence these predicates are
	now unsafe */
  InitCPred("$compile", 3, p_compile, SyncPredFlag);
  InitCPred("$compile_dynamic", 4, p_compile_dynamic, SyncPredFlag);
  InitCPred("$purge_clauses", 2, p_purge_clauses, SafePredFlag|SyncPredFlag);
  InitCPred("$in_use", 2, p_in_use, TestPredFlag | SafePredFlag|SyncPredFlag);
  InitCPred("$is_dynamic", 2, p_is_dynamic, TestPredFlag | SafePredFlag);
  InitCPred("$number_of_clauses", 3, p_number_of_clauses, SafePredFlag|SyncPredFlag);
  InitCPred("$undefined", 2, p_undefined, SafePredFlag|TestPredFlag);
  InitCPred("$optimizer_on", 0, p_optimizer_on, SafePredFlag|SyncPredFlag);
  InitCPred("$clean_up_dead_clauses", 0, p_clean_up_dead_clauses, SyncPredFlag);
  InitCPred("$optimizer_off", 0, p_optimizer_off, SafePredFlag|SyncPredFlag);
  InitCPred("$kill_dynamic", 2, p_kill_dynamic, SafePredFlag|SyncPredFlag);
  InitCPred("$in_this_file_before", 3, p_in_this_f_before, SafePredFlag);
  InitCPred("$first_clause_in_file", 3, p_first_cl_in_f, SafePredFlag);
  InitCPred("$mk_cl_not_first", 2, p_mk_cl_not_first, SafePredFlag);
  InitCPred("$new_multifile", 3, p_new_multifile, SafePredFlag|SyncPredFlag);
  InitCPred("$is_multifile", 2, p_is_multifile, TestPredFlag | SafePredFlag);
  InitCPred("$is_profiled", 1, p_is_profiled, SafePredFlag|SyncPredFlag);
  InitCPred("$profile_info", 3, p_profile_info, SafePredFlag|SyncPredFlag);
  InitCPred("$profile_reset", 2, p_profile_reset, SafePredFlag|SyncPredFlag);
  InitCPred("$toggle_static_predicates_in_use", 0, p_toggle_static_predicates_in_use, SafePredFlag|SyncPredFlag);
  InitCPred("$set_pred_module", 2, p_set_pred_module, SafePredFlag);
  InitCPred("$parent_pred", 3, p_parent_pred, SafePredFlag);
  InitCPred("$system_predicate", 2, p_system_pred, SafePredFlag);
  InitCPred("$cut_transparent", 1, p_cut_transparent, SafePredFlag);
}

