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

one sig Counter {
    var length: one Int
}

one sig Satisfiable {
    var flag: lone Boolean
}

sig Clause {
	litset: set Literal->Boolean
}

sig Assignment {
	var branch: lone Assignment,
    var assigned: set Literal->Boolean,
    var implied: set Literal->Boolean
}

one sig Root extends Assignment {}

//TODO: all of these could be properties
// pred wellFormed {
//     // TODO: 'always wellFormed' to enforce always wellformedness
//     -- next is Linear
//     branch.~branch in iden
//     no branch.Root
//     //Assignment->Assignment in *(next + ~next) 

//     -- lit is Bijection between Literals and assignments
//     lit.~lit in iden
//     Literal in Assignment.lit

//     -- All literals appear at least once
//     Literal in Clause.litset.Boolean
//     Clause in (litset.Boolean).Literal
// }

----------------
-- Predicates --
----------------

pred unSat {
    some c : Clause | {
        all l : c.litset.Boolean | {
            some l.(Assignment.assigned + Assignment.implied)
            l.(Assignment.assigned + Assignment.implied) not in l.(c.litset)
        }
    }
}

pred init {
    length = Counter->sing[0]
    no implied
    no branch
    no assigned
    no flag
}

// fun getBottomNull: Assignment { 
//     (Assignment - guessed.Boolean) - (Assignment - guessed.Boolean).next
// }

pred increment {
    length' = Counter->sing[add[1, sum[Counter.length]]]
}

fun getTopTrue: Assignment { 
    (assigned.True).Literal - (((assigned.True).Literal).(^~branch))
}

pred backtrack {
    -- Guard
    unSat
    
    -- Transition
    flag' = flag
    branch' = (*branch.getTopTrue)->(*branch.getTopTrue) & branch
    assigned' = (assigned & ((branch').Assignment)->Literal->Boolean) + getTopTrue->(getTopTrue.assigned.True)->False
    implied' = implied & ((branch').Assignment)->Literal->Boolean
}

fun getLastAssigned: Assignment {
    (Root.*branch - branch.(Root.*branch))
}

fun getNewAssigned: Assignment {
    (Root.*(branch') - (branch').(Root.*(branch')))
}

pred guessNext {
    -- Guard
    not unSat

    -- Transition
    flag' = flag
    implied' = implied
    
    one l: Literal - Root.*branch.(assigned + implied).Boolean | {
        some Root.assigned => {assigned' = assigned + getNewAssigned->l->True}
        else {assigned' = Root->l->True}
    }

    some Root.assigned => {
        one a: Assignment - (Root.*branch) | {
            branch' = branch + getLastAssigned->a
            //some branch => {branch' = branch + getLastAssigned->a}
            //else {branch' = Root->a}
        }
    }
    else {branch' = branch}

}


pred moves {
    backtrack or 
    guessNext
}


pred returnSat {
    all c : Clause | {
        some l : c.litset.Boolean | {
            some l.(Assignment.assigned + Assignment.implied)
            l.(Assignment.assigned + Assignment.implied) in l.(c.litset)
        }
    }

    -- Transition
    branch' = branch
    flag' = Satisfiable->True
    assigned' = assigned
    implied' = implied
    length' = length
}

-- We may not need this
// pred fillTrue {
//     guessed' = guessed + (Assignment - guessed.Boolean)->True
//     flag' = flag
//     assigned' = assigned
//     implied' = implied
// }

pred returnUnsat {
    -- Guard
    unSat
    Literal.(Assignment.assigned) = False
    
    -- Transition
    assigned' = assigned
    flag' = Satisfiable->False
    implied' = implied
    branch' = branch
    length' = length
}

pred stutter {
    --Invariant
    branch' = branch
    flag' = flag
    assigned' = assigned
    implied' = implied
    length' = length
}

pred traces {
    // wellFormed
    init
    always {(returnSat or returnUnsat) => {after stutter} else {moves and increment}}
}


-------------
-- Testing --
-------------

run {traces and {eventually returnSat or returnUnsat} and {eventually sum[Counter.length] > 6}} for 10 Assignment, exactly 3 Clause, exactly 7 Int
