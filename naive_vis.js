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

// Extract assignments
const assignmentMap = {}
for (const l of Literal.atoms()) {
    const sign = lit.join(l).join(guessed).tuples(true).map(x => x.atoms(true)[0]).map(x => x._id)
    assignmentMap[l._id] = sign
}

console.log(assignmentMap)

// Print clauses.
const assignmentTable = document.createElement('table')
for (const k in assignmentMap) {
    const tr = document.createElement('tr')
    assignmentTable.appendChild(tr)

    const td = document.createElement('td')
    tr.appendChild(td)
    tr.textContent = k + ": " + assignmentMap[k]
}

// Print out
div.innerHTML = ''
div.appendChild(document.createTextNode("Clauses:"))
div.appendChild(clauseTable)
div.appendChild(document.createElement('hr'))
div.appendChild(document.createTextNode("Assignments:"))
div.appendChild(assignmentTable)
