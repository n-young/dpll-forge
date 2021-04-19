#lang forge

option problem_type temporal
option max_tracelength 24
option min_tracelength 4

-----------------------------
-- CSCI 1710 Final Project --
--       Nick Young        --
--       Derick Toth       --
--       Matt Shinkar      --
--   TA Mentor: tdelveccc   --
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

one sig Counter {
    var len: one Int
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
    ((getCurrLitset.False).Literal - getNotSattedClauses.((getCurrLitset.False).(Literal->Literal - iden).~(getCurrLitset.False) & iden))) - 
    {c : Clause | no c.litset}
}

fun mostRecentGuess: one Assignment {
    (Root.*next - next.(Root.^(next)))
}

fun getUIPs[conflict : Clause, guess : GuessedAssignment]: set Assignment {
    {UIP : Assignment | {
        guess->guess not in ^((implied + (assigned.Boolean).(conflict.litset.Boolean)->guess) - UIP->Assignment - Assignment->UIP )}}
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

pred BCP {
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
    some c : Clause | {
        some c.litset
        all l : c.litset.Boolean | {
            some l.(Assignment.assigned)
            l.(Assignment.assigned) not in l.(c.litset)
            // We have selected the conflict clause c
        }
        some added : Clause - (litset.Boolean).Literal | {
            litset' = litset + added->learnedClause[c,mostRecentGuess]
            newDecisionLevel[learnedClause[c,mostRecentGuess],mostRecentGuess] = none implies { //We are learning a unit clause
                next' = next - GuessedAssignment->mostRecentGuess
                implied' = implied - Assignment->(mostRecentGuess.^implied)
                assigned' = assigned - (mostRecentGuess.*implied)->Literal->Boolean
            } else {
                next' = next - GuessedAssignment->(newDecisionLevel[learnedClause[c,mostRecentGuess],mostRecentGuess].^next)
                implied' = implied - Assignment->((newDecisionLevel[learnedClause[c,mostRecentGuess],mostRecentGuess].*next).^implied)
                assigned' = assigned - ((newDecisionLevel[learnedClause[c,mostRecentGuess],mostRecentGuess].^next).*implied)->Literal->Boolean
            }
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
    len' = len
}


-- =======================================================================
-- HOUSEKEEPING
-- =======================================================================

pred init {
    no assigned
    no implied
    no next
    no flag
    len = Counter->sing[0]
    Literal in Clause.litset.Boolean
}

pred moves {
    {impliedConflict or returnSat} implies {
        stutter
    } else {
        len' = Counter->sing[add[sum[Counter.len], 1]]
        {existsConflict} implies {
            backtrack
        } else {
            {canDoBCP} implies {
                BCP
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
    Root = A0
    assigned = A0->L1->False0 + A1->L2->True0
    implied = A0->A1

    no next
    flag = Satisfiable0->True0
}
// test expect {
//     backtrack_case_1: { traces and eventually backtrack } for SatCase1 is sat 
// }

//  run {//some c : Clause - (litset.Boolean).Literal {
//      litset' = litset + c->(Literal - Clause.litset.False)->True}
    // flag' = flag
    // after no assigned or some assigned
    // after no implied
    // after no next
    // } for BacktrackCase1


pred PUnsatCase1 {
    some L1, L3: Literal | {
        #(L1 + L3) = 2
        some C1, C2, C3: Clause | {
            #(C1 + C2 + C3) = 3
            litset = C1->L1->False + C2->L1->True + C2->L3->True + C3->L1->True
        }
    }
}

pred PUnsatCase2 {
    some Literal0, Literal1, Literal2: Literal | {
        #(Literal0 + Literal1 + Literal2) = 3
        some Clause1, Clause2, Clause3, Clause4: Clause | {
            #(Clause1 + Clause2 + Clause3 + Clause4) = 4
            litset = Clause1->Literal1->False + Clause1->Literal2->True + Clause2->Literal1->True + Clause2->Literal2->True + Clause3->Literal0->False + Clause3->Literal2->False + Clause4->Literal0->True + Clause4->Literal2->False
        }
    }
}

pred generatedCase1 {
    some L1, L3, L2 : Literal | {
        #(L1 + L3 + L2) = 3
        some C0, C1 : Clause | {
            #(C0 + C1) = 2
            litset = C0->L1->True + C0->L3->False + C1->L2->True + C1->L3->True + C1->L1->False
        }
    }
}

-- =======================================================================
-- RUN
-- =======================================================================

run {traces and PUnsatCase2} for 10 Clause

// run {traces and eventually impliedConflict and eventually sum[Counter.len] > 3} for 5 Clause, exactly 3 Literal, 3 Assignment

// run {traces and eventually returnSat and eventually backtrack and eventually sum[Counter.len] > 3} for 5 Clause, exactly 3 Literal, 3 Assignment
