#lang forge

sig Atom {edges: set Atom}

pred isDAG {
    no iden & ^edges
    Atom->Atom in ^(edges + ~edges)

    one Atom - Atom.edges
    one Atom - edges.Atom
}

pred hasInflection {
    some a : Atom -(Atom - edges.Atom)-(Atom - Atom.edges){
        no (Atom - edges.Atom) & (Atom - Atom.edges).^(edges & ((Atom-a) -> (Atom-a)))
    }
}

run {isDAG and hasInflection} for exactly 3 Atom