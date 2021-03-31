#lang forge
-----------------------------
-- CSCI 1710 Final Project --
--       Yung Thot         --
--       Derick Thot       --
--       Matt Thot         --
--   TA Mentor: TDel Thot  --
-----------------------------


--TODO
--Check that null only comes after T/F assignments

option problem_type temporal
option max_tracelength 20

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

----------------
-- Predicates --
----------------

pred unSat {
    some c : Clause | (
        all l : c.litset.Boolean | (
            some (lit.l).guessed and
            ((lit.l).guessed not in l.(c.litset))
            --l.(c.litset) != (lit.l).guessed 
        )
    )
}

pred init {
    no guessed
}

fun getBottomNull: Assignment { 
    (Assignment - guessed.Boolean) - (Assignment - guessed.Boolean).next
}

fun getTopTrue: Assignment { 
    guessed.True - ((guessed.True).(^~next))
}

pred backtrack {
    -- Guard
    unSat

    -- Transition
    guessed' = (guessed & ((^next.getTopTrue)->Boolean)) + getTopTrue->False
}

pred guessNext {
    -- Guard
    not unSat

    -- Transition
    guessed' = guessed + getBottomNull->True
}

pred moves {
    backtrack or 
    guessNext
}


pred returnSat {
    all c : Clause | (
        some l : Literal | (
            l in (guessed.Boolean).lit and
            l in c.litset.Boolean and
            (lit.l).guessed in l.(c.litset)
        )
    )
}

-- We may not need this
pred fillTrue {
    guessed' = guessed + (Assignment - guessed.Boolean)->True
}

pred returnUnsat {
    -- Guard
    unSat

    Assignment.guessed = False
}

pred stutter {
    --Invariant
    guessed = guessed'
}

pred traces {
    wellFormed

    init

    always {
        (returnSat or returnUnsat) => {stutter} else {moves}
    }
}


-------------
-- Testing --
-------------

run {traces and eventually returnUnsat}