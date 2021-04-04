#lang forge

option problem_type temporal
option max_tracelength 24

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
	var branch: lone Assignment,
    var assigned: set Literal->Boolean,
    var implied: set Literal->Boolean
}
one sig Root extends Assignment {}

one sig Satisfiable {
    var flag: lone Boolean
}

one sig Counter {
    var length: one Int
}


-- =======================================================================
-- FUNCTIONS
-- =======================================================================

fun getTopTrue: Assignment { 
    (assigned.True).Literal - (((assigned.True).Literal).(^~branch))
}

fun getLastAssigned: Assignment {
    (Root.*branch - branch.(Root.*branch))
}

fun getNewAssigned: Assignment {
    (Root.*(branch') - (branch').(Root.*(branch')))
}

fun getSattedClauses: set Clause {
    (litset.True).((Assignment.(assigned + implied)).True) + (litset.False).((Assignment.(assigned + implied)).False)
}

fun getNotSattedClauses: set Clause {
    -- will also return 'empty' unsat clauses (but don't worry :))
    Clause - getSattedClauses
}

fun getCurrLitset: set Clause->Literal->Boolean {
    litset & getNotSattedClauses->(Literal - Assignment.(assigned + implied).Boolean)->Boolean
}

fun getUnitClauses: set Clause {
    -- a clause isn't a unit clause if you can do clause->literal->different literal->same clause
    -- duplicate is symmetric difference (ie. C->3->T and C->3->F is NOT A UNIT CLAUSE)
    (getNotSattedClauses - getNotSattedClauses.((getCurrLitset.Boolean).(Literal->Literal - iden).~(getCurrLitset.Boolean) & iden)) - 
    (((getCurrLitset.True).Literal - getNotSattedClauses.((getCurrLitset.True).(Literal->Literal - iden).~(getCurrLitset.True) & iden)) & 
    ((getCurrLitset.False).Literal - getNotSattedClauses.((getCurrLitset.False).(Literal->Literal - iden).~(getCurrLitset.False) & iden)))
}

fun getPureLits: set Literal {
    (Literal - Assignment.(assigned + implied).Boolean) - Literal.(iden & ((getNotSattedClauses.getCurrLitset).(True->False + False->True).~(getNotSattedClauses.getCurrLitset)))
}


-- =======================================================================
-- PREDICATES
-- =======================================================================

pred unSat {
    (~(Assignment.(assigned + implied)).(Assignment.(assigned + implied)) not in iden) or 
    (some c : Clause | {
        all l : c.litset.Boolean | {
            some l.(Assignment.assigned + Assignment.implied)
            l.(Assignment.assigned + Assignment.implied) not in l.(c.litset)
        }
    })
}

pred canDoSomeUnitElim {
    some l: Literal - Root.*branch.(assigned + implied).Boolean | {
        some c: Clause | {
            (c.getCurrLitset = l->True) or (c.getCurrLitset = l->False)
        }
    }
}

pred canDoSomePureElim {
    some l: Literal - Root.*branch.(assigned + implied).Boolean | {
        (l.(getNotSattedClauses.getCurrLitset) = True) or (l.(getNotSattedClauses.getCurrLitset) = False)
    }
}


-- =======================================================================
-- TRANSITIONS
-- =======================================================================

pred unitClauseElim {
    -- Guard
    canDoSomeUnitElim
    not unSat

    -- Transition
    flag' = flag
    assigned' = assigned
    branch' = branch
    implied' = implied + getLastAssigned->(getUnitClauses.getCurrLitset)
}

pred pureLitElim {
    -- Guard
    canDoSomePureElim
    not unSat
    
    --Transition
    flag' = flag
    assigned' = assigned
    branch' = branch
    implied' = implied + getLastAssigned->(Clause.getCurrLitset & getPureLits->Boolean)
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
        }
    } else {branch' = branch}
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

pred returnSat {
    -- Guard
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

pred returnUnsat {
    -- Guard
    unSat
    Literal.(Assignment.assigned) = False or no Literal.(Assignment.assigned)
    
    -- Transition
    assigned' = assigned
    flag' = Satisfiable->False
    implied' = implied
    branch' = branch
    length' = length
}


-- =======================================================================
-- HOUSEKEEPING
-- =======================================================================

pred init {
    Clause in (litset.Boolean).Literal
    Literal in Clause.litset.Boolean
    length = Counter->sing[0]
    no implied
    no branch
    no assigned
    no flag
}

pred moves {
    unSat => backtrack
    else {
        canDoSomeUnitElim => unitClauseElim
        else {
            canDoSomePureElim => pureLitElim
            else {
                guessNext
            }
        }
    }
}

pred increment {
    length' = Counter->sing[add[1, sum[Counter.length]]]
}

pred stutter {
    branch' = branch
    flag' = flag
    assigned' = assigned
    implied' = implied
    length' = length
}

pred traces {
    init
    always {(returnSat or returnUnsat) => {after stutter} else {moves and increment}}
}


-- =======================================================================
-- PROPERTY CHECKS
-- NOTE: These are all definitely correct, but they take too long to run
-- =======================================================================

-- Vacuity check.
// test expect {
//     vacuity: { traces } is sat
//     always_finishes: { traces implies eventually { returnUnsat or returnSat } } is sat
// }

-- Check that if the current case will eventually be unsat, we never reach a sat case.
// test expect {
//     eventually_unsat: { traces implies { eventually returnUnsat implies always not returnSat } } is theorem
// }

-- Check that if the guessed enum is full, the flag exists
// test expect {
//     must_terminate: { traces implies always { Literal in Assignment.assigned.Boolean implies { unSat or after some flag } } } is theorem
// }

-- Check that the flag is always raised correctly?
// test expect {
//     flag_sat: { traces implies always { Satisfiable.flag = True implies returnSat } } is theorem
//     flag_unsat: { traces implies always { Satisfiable.flag = False implies returnUnsat } } is theorem
// }

-- Check that branch is always linear.
// test expect {
//     branch_linear: { traces implies always {
//         branch.~branch in iden
//         (Root.*branch)->(Root.*branch) in *(branch + ~branch)
//         one a: Assignment | { a in Root.*branch } and { no a.branch }
//     } } is theorem
// }

-- Check that assigned is always one per Assignment, and one Boolean per Literal.
// test expect {
//     assigned_injective: {
//         traces implies always {
//             (assigned.Boolean).~(assigned.Boolean) in iden
//         }
//     } is theorem
//     no_double_assign: {
//         traces implies always {
//             ~(Assignment.assigned).(Assignment.assigned) in iden
//         }
//     } is theorem
// }

-- In between an assignment of true and false of a particular literal, must have an unsat in between
// test expect {
//     in_between: {
//         all l: Literal | {
//             l.(Assignment.assigned) = False implies {
//                 historically unSat and l.(Assignment.assigned) = True 
//             }
//         }
//     } is theorem
// }

-- Check that if we have an empty clause, that we return Unsat.
// test expect {
//     empty_clauses: {
//         traces and { some c: Clause | c in getNotSattedClauses and no c.litset } implies {
//             after unSat
//         }
//     } is theorem
// }


-- =======================================================================
-- CONCRETE CASES
-- =======================================================================

-- TODO: More concrete cases

inst SatCase1 {
    Literal = L1 + L2 + L3
    Clause = C1 + C2 + C3
    litset = C1->L1->True0 + C2->L1->True0 + C2->L2->True0 + C3->L3->False0
}
test expect {
    sat_case_1: { traces and eventually returnSat } for SatCase1 is sat 
}

inst UnsatCase1 {
    Literal = L1 + L2 + L3
    Clause = C1 + C2 + C3
    litset = C1->L1->False0 + C2->L1->True0 + C2->L3->True0 + C3->L1->True0
}
test expect {
    unsat_case_1: { traces and eventually returnSat } for UnsatCase1 is unsat 
}


-- =======================================================================
-- RUN
-- =======================================================================

-- Unsat Case
-- run {traces and {eventually returnUnsat}} for exactly 6 Assignment, exactly 3 Literal, exactly 3 Clause, 7 Int

-- Sat Case
-- run {traces and {eventually returnSat}} for exactly 6 Assignment, exactly 3 Literal, exactly 3 Clause, 7 Int

-- Longer trace lengths
-- run {traces and {eventually returnUnsat or returnSat} and {eventually sum[Counter.length] > 4}}
--      for exactly 6 Assignment, exactly 3 Literal, exactly 3 Clause, 7 Int

-- Concrete case
-- run { traces } for 7 Int for SatCase1 
