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
	var litset: set Literal->Boolean
}

abstract sig Assignment {
    var assigned: set Literal->Boolean
    var implies: set Assignment
}

sig GuessedAssignment extends Assignment {
    var next : lone GuessedAssignment
}

one sig Root extends GuessedAssignment {}

sig ImpliedAssignment extends Assignment {}

one sig Satisfiable {
    var flag: lone Boolean
}

one sig Counter {
    var length: one Int
}


-- =======================================================================
-- FUNCTIONS
-- =======================================================================

fun getSattedClauses: set Clause {
    (litset.True).(Assignment.assigned.True) + (litset.False).(Assignment.assigned.False)
}

fun getNotSattedClauses: set Clause {
    -- will also return 'empty' unsat clauses (but don't worry :))
    Clause - getSattedClauses
}

fun getCurrLitset: set Clause->Literal->Boolean {
    litset & getNotSattedClauses->(Literal - Assignment.assigned.Boolean)->Boolean
}

fun getUnitClauses: set Clause {
    -- a clause isn't a unit clause if you can do clause->literal->different literal->same clause
    -- duplicate is symmetric difference (ie. C->3->T and C->3->F is NOT A UNIT CLAUSE)
    (getNotSattedClauses - getNotSattedClauses.((getCurrLitset.Boolean).(Literal->Literal - iden).~(getCurrLitset.Boolean) & iden)) - 
    (((getCurrLitset.True).Literal - getNotSattedClauses.((getCurrLitset.True).(Literal->Literal - iden).~(getCurrLitset.True) & iden)) & 
    ((getCurrLitset.False).Literal - getNotSattedClauses.((getCurrLitset.False).(Literal->Literal - iden).~(getCurrLitset.False) & iden)))
}

-- =======================================================================
-- PREDICATES
-- =======================================================================

// Commenting out Conflict Literal Stuff because we only assign truth value in BCP
// pred existsConflictLiteral {
//     (~(Assignment.assigned).(Assignment.assigned) not in iden) 
// }

pred existsConflictClause {
    (some c : Clause | {
        all l : c.litset.Boolean | {
            some l.(Assignment.assigned)
            l.(Assignment.assigned) not in l.(c.litset)
        }
    })
}

pred existsConflict {
    //existsConflictLiteral or 
    existsConflictClause
}

pred canDoBCP {
    some l: Literal - Assignment.assigned.Boolean | {
        some c: Clause | {
            (c.getCurrLitset = l->True) or (c.getCurrLitset = l->False)
        }
    }
}

pred sat {
    no getNotSattedClauses
}

pred impliedConflict { //Return Unsat
    // //Implied Conflict Lit
    // (some l : Assignment.assigned.Boolean | {
    //     l->Boolean in Assignment.assigned

    //     no GuessedAssignment & ((assigned.Boolean).l).~*implies
    // })
    // or //Implied Conflict Clause
    (some c : Clause | {
        all l : c.litset.Boolean | {
            some l.(Assignment.assigned)
            l.(Assignment.assigned) not in l.(c.litset)
        }

        no GuessedAssignment & (assigned.((c.litset).Boolean)).(~*implies)
    })
}

-- =======================================================================
-- TRANSITIONS
-- =======================================================================

pred bockAndCallPorture {
    -- Guard
    canDoBCP
    not existsConflict

    -- Transition
    flag' = flag
    next' = next
    litset' = litset
    one c : getUnitClauses {
        one a : Assignment - (assigned.Boolean).Literal {
            assigned' = assigned + a->(c.getCurrLitset)
            implies' = implies + ((assigned.Boolean).(c.litset - c.getCurrLitset))->a
        }
    }

}

pred makeGuess {
    -- Guard
    not existsConflict

    -- Transition
    flag' = flag
    implies' = implies
    litset' = litset
    one l : Literal - Assignment.assigned.Boolean | {
        one a : Assignment - (assigned.Boolean).Literal | {
            assigned' = assigned + a->l->True

            {some Root.assigned} => {
                next' = next + (Root.*next - next.(Root.^(next)))->a
            } else {
                a = Root
                next' = next
            }
        }
    }
}

pred backtrack {
    -- Guard

    -- Transition

}


-- =======================================================================
-- HOUSEKEEPING
-- =======================================================================

pred init {
    no assigned
    no implies
    no next
    length = sing[0]
    no flag
}

pred moves {}

pred increment {}

pred stutter {}

pred traces {
    init
}



run {traces and eventually sum[Counter.length] > 5} for exactly 5 Literal, exactly 5 Assignment, 7 Int

-- =======================================================================
-- PROPERTY CHECKS
-- NOTE: These are all definitely correct, but they take too long to run
-- =======================================================================

-- =======================================================================
-- CONCRETE CASES
-- =======================================================================

-- =======================================================================
-- RUN
-- =======================================================================
