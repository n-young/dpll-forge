#lang forge

option problem_type temporal



-----------------------------
-- CSCI 1710 Final Project --
--       Yung Thot         --
--       Derick Thot       --
--       Matt Thot         --
--   TA Mentor: TDel Thot  --
-----------------------------

// Setbuilding: {x, y: Literal | x != y}
// "Less than" relation, fixes backtracking


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
    var assigned: set Literal->Boolean,
    var implied: set Assignment
}

sig GuessedAssignment extends Assignment {
    var next : lone GuessedAssignment
}

one sig Root extends GuessedAssignment {}

sig ImpliedAssignment extends Assignment {}

one sig Satisfiable {
    var flag: lone Boolean
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

fun mostRecentGuess: one Assignment {
    (Root.*next - next.(Root.^(next)))
}

fun getUIPs[conflict : Clause, guess : GuessedAssignment]: set Assignment {
    {UIP : Assignment | {
        ((assigned.Boolean).(conflict.litset.Boolean) & guess.*implied) not in {
            guess.^(implied - UIP->Assignment - Assignment->UIP)
        }
    }}
}

fun firstUIP[conflict : Clause, guess : GuessedAssignment]: one Assignment {
    getUIPs[conflict,guess] - ((^implied).(getUIPs[conflict,guess]) & getUIPs[conflict,guess])
}

fun learnedClause[conflict : Clause, guess : GuessedAssignment]: set Literal->Boolean {
    (firstUIP[conflict,guess] + ((((assigned.Boolean).(conflict.litset.Boolean)).(
                    ~^(implied - firstUIP[conflict,guess]->Assignment - Assignment->firstUIP[conflict,guess])
                )) & GuessedAssignment)).assigned.(True->False + False->True)
}

fun newDecisionLevel[learned : Literal->Boolean, guess : GuessedAssignment] : one Assignment {
   ((((assigned.Boolean).(learned.Boolean)) & GuessedAssignment) - guess) -
   ^next.((((assigned.Boolean).(learned.Boolean)) & GuessedAssignment) - guess)
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
        some c.litset
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

pred returnSat {
    no getNotSattedClauses
}

pred impliedConflict { //Return Unsat
    // //Implied Conflict Lit
    // (some l : Assignment.assigned.Boolean | {
    //     l->Boolean in Assignment.assigned

    //     no GuessedAssignment & ((assigned.Boolean).l).~*implied
    // })
    // or //Implied Conflict Clause
    (some c : Clause | {
        some c.litset
        all l : c.litset.Boolean | {
            some l.(Assignment.assigned)
            l.(Assignment.assigned) not in l.(c.litset)
        }

        no GuessedAssignment & ((assigned.Boolean).((c.litset).Boolean)).(~*implied)
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
        one a : ImpliedAssignment - (assigned.Boolean).Literal {
            assigned' = assigned + a->(c.getCurrLitset)
            implied' = implied + ((assigned.Boolean).((c.litset - c.getCurrLitset).Boolean))->a
        }
    }

}

pred makeGuess {
    -- Guard
    not existsConflict

    -- Transition
    flag' = flag
    implied' = implied
    litset' = litset
    one l : Literal - Assignment.assigned.Boolean | {
        one a : GuessedAssignment - (assigned.Boolean).Literal | {
            assigned' = assigned + a->l->True

            {some Root.assigned} => {
                next' = next + mostRecentGuess->a
            } else {
                a = Root
                next' = next
            }
        }
    }
}

pred backtrack {
    -- Guard
    existsConflict and 
    not impliedConflict

    -- Transition
    flag' = flag
    one c : Clause | {
        some c.litset
        all l : c.litset.Boolean | {
            some l.(Assignment.assigned)
            l.(Assignment.assigned) not in l.(c.litset)
            // We have selected the conflict clause c
        }
        one added : Clause - (litset.Boolean).Literal | {
            litset' = litset + added->learnedClause[c,mostRecentGuess]
            next' = next - GuessedAssignment->(newDecisionLevel[learnedClause[c,mostRecentGuess],mostRecentGuess].^next)
            implied' = implied - Assignment->((newDecisionLevel[learnedClause[c,mostRecentGuess],mostRecentGuess].*next).^implied)
            assigned' = assigned - ((newDecisionLevel[learnedClause[c,mostRecentGuess],mostRecentGuess].^next).*implied)->Literal->Boolean
        }
    }
}

pred stutter {
    assigned' = assigned
    next' = next
    litset' = litset
    implied' = implied
    returnSat implies {
        flag' = Satisfiable->True
    } else {
        flag' = Satisfiable->False
    }
}


-- =======================================================================
-- HOUSEKEEPING
-- =======================================================================

pred init {
    no assigned
    no implied
    no next
    no flag
    Literal in Clause.litset.Boolean
}

pred moves {
    {impliedConflict or returnSat} implies {
        stutter
    } else {
        {existsConflict} implies {
            backtrack
        } else {
            {canDoBCP} implies {
                bockAndCallPorture
            } else {
                makeGuess
            }
        }
    }
}

pred traces {
    init
    always moves
}

option max_tracelength 24
option min_tracelength 4

// run {traces and eventually backtrack} for exactly 4 Literal,  10 Assignment, 10 Clause

-- =======================================================================
-- PROPERTY CHECKS
-- NOTE: These are all definitely correct, but they take too long to run
-- =======================================================================



-- =======================================================================
-- CONCRETE CASES
-- =======================================================================

inst BacktrackCase1 {
    Literal = L1 + L2
    Clause = C1 + C2 + C3
    litset = C1->L1->True0 + C1->L2->True0 + C2->L1->True0 + C2->L2->False0

    Assignment = A0 + A1
    GuessedAssignment = A0
    ImpliedAssignment = A1
    assigned = A0->L1->False0 + A1->L2->True0

    no next
    no flag
}
// test expect {
//     backtrack_case_1: { traces and eventually backtrack } for SatCase1 is sat 
// }

run { backtrack and after always stutter} for BacktrackCase1

-- =======================================================================
-- RUN
-- =======================================================================
