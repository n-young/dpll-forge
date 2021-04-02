// Convert a literal to a string
function litToString(literal, sign) {
    if (sign.includes("True")) {
        return literal.substring(literal.length - 1)
    } else {
        return "-" + literal.substring(literal.length - 1)
    }
}

// Extract clauses.
const clauseMap = {}
litset.tuples(true)
    .map(x => x.atoms(true))
    .map(x => x.map(y => y._id))
    .forEach(x => {
        if (x[0] in clauseMap) {
            clauseMap[x[0]].push(litToString(x[1], x[2]))
        } else {
            clauseMap[x[0]] = [litToString(x[1], x[2])]
        }
    })

// Print clauses.
const clauseTable = document.createElement('table')
for (const k in clauseMap) {
    const tr = document.createElement('tr')
    clauseTable.appendChild(tr)

    const td = document.createElement('td')
    tr.appendChild(td)
    tr.textContent = k + ": " + clauseMap[k].join(", ")
}

// Extract 
const assignmentMap = {}
for (const l of Literal.atoms()) {
    const sign = l.join(Assignment.join(assigned)).tuples(true).map(x => x.atoms(true)).map(x => x[0]._id)
        + l.join(Root.join(assigned)).tuples(true).map(x => x.atoms(true)).map(x => x[0]._id)
    if (sign) { assignmentMap[l._id] = sign }
}

const impliedMap = {}
for (const l of Literal.atoms()) {
    const sign = l.join(Assignment.join(implied)).tuples(true).map(x => x.atoms(true)).map(x => x[0]._id)
        + l.join(Root.join(implied)).tuples(true).map(x => x.atoms(true)).map(x => x[0]._id)
    if (sign) { impliedMap[l._id] = sign }
}

// Print assignments.
const assignments = document.createElement('p')
for (const k in assignmentMap) {
    assignments.innerHTML += litToString(k, assignmentMap[k]) + ", "
}
for (const k in impliedMap) {
    assignments.innerHTML += "<span style='color: red'>" + litToString(k, assignmentMap[k]) + "</span>" + ", "
}

// Check if satisfied
let flag_str = flag.tuples(true).map(x => x.atoms(true)).map(x => x[1]._id)[0]

// Print out
div.innerHTML = ''
div.appendChild(document.createTextNode("Clauses:"))
div.appendChild(clauseTable)
div.appendChild(document.createElement('hr'))
div.appendChild(document.createTextNode("Assignments:"))
div.appendChild(assignments)

// Print sat string if it exists
if (flag_str) {
    let sat_str = flag_str.includes("True") ? "SAT" : "UNSAT"
    div.appendChild(document.createTextNode(sat_str))
}
