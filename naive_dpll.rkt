#lang forge

option problem_type temporal
option max_tracelength 20

-----------------------------
-- CSCI 1710 Final Project --
--       Yung Thot         --
--       Derick Thot       --
--       Matt Thot         --
--   TA Mentor: TDel Thot  --
-----------------------------


-- =======================================================================
-- SIGNATURES
-- =======================================================================

abstract sig Boolean {}
one sig True extends Boolean {}
one sig False extends Boolean {}

sig Literal {}

sig Clause {
	litset: set Literal->Boolean
}

sig Assignment {
	lit: one Literal,
    var guessed: lone Boolean,
	next: lone Assignment
}
one sig Root extends Assignment {}

one sig Satisfiable {
    var flag: lone Boolean
}

pred wellFormed {
    -- next is Linear
    next.~next in iden
    no next.Root
    Assignment->Assignment in *(next + ~next) 

    -- lit is Bijection between Literals and assignments
    lit.~lit in iden
    Literal in Assignment.lit

    -- All literals appear at least once
    Literal in Clause.litset.Boolean
    Clause in (litset.Boolean).Literal
}

-- =======================================================================
-- FUNCTIONS
-- =======================================================================

fun getBottomNull: Assignment { 
    (Assignment - guessed.Boolean) - (Assignment - guessed.Boolean).next
}

fun getTopTrue: Assignment { 
    guessed.True - ((guessed.True).(^~next))
}


-- =======================================================================
-- PREDICATES AND TRANSITIONS
-- =======================================================================

pred unSat {
    some c : Clause | (
        all l : c.litset.Boolean | (
            some (lit.l).guessed and ((lit.l).guessed not in l.(c.litset))
            --l.(c.litset) != (lit.l).guessed 
        )
    )
}

pred guessNext {
    -- Guard
    not unSat

    -- Transition
    guessed' = guessed + getBottomNull->True
    flag' = flag
}

pred backtrack {
    -- Guard
    unSat
    
    -- Transition
    guessed' = (guessed & ((^next.getTopTrue)->Boolean)) + getTopTrue->False
    flag' = flag
}

pred returnSat {
    all c : Clause | (
        some l : Literal | (
            l in (guessed.Boolean).lit and
            l in c.litset.Boolean and
            (lit.l).guessed in l.(c.litset)
        )
    )

    -- Transition
    guessed' = guessed
    flag' = Satisfiable->True
}

pred returnUnsat {
    -- Guard
    unSat
    Assignment.guessed = False
    
    -- Transition
    guessed' = guessed
    flag' = Satisfiable->False
}

pred init {
    no guessed
    no flag
}

pred stutter {
    --Invariant
    guessed = guessed'
    flag' = flag
}
pred moves {
    backtrack or 
    guessNext
}

pred traces {
    wellFormed
    init
    always { (returnSat or returnUnsat) => {after stutter} else {moves} }
}


-- =======================================================================
-- RUN
-- =======================================================================

run {traces and {eventually returnSat or returnUnsat}} for exactly 3 Assignment
