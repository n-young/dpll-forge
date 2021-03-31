#lang forge
-----------------------------
-- CSCI 1710 Final Project --
--       Yung Thot         --
--       Derick Thot       --
--       Matt Thot         --
-----------------------------


--TODO
--Check that null only comes after T/F assignments

option problem_type temporal

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
}

pred init {

}

pred traces {

}

run {wellFormed} for exactly 4 Assignment