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
for (const l of assigned.tuples()) {
  const atoms = l.atoms()
  const literal = atoms[1]._id
  const sign = atoms[2]._id
  assignmentMap[literal] = sign
}

// Print assignments.
const assignments = document.createElement('p')
for (const k in assignmentMap) {
    assignments.innerHTML += litToString(k, assignmentMap[k]) + ", "
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

// Create canvas
const graph = document.createElement('div')
graph.setAttribute('id', 'my_dataviz')
div.appendChild(graph)

// yoinked code :))
const node_ids = {}
const nodes = assigned.tuples().map(x => x.atoms()).map((x, i) => {
  node_ids[x[0]._id] = i
  console.log(x)
  return {
    id: i,
    name: x[1]._id,
    sign: x[2]._id
  }
})


const links = implied.tuples().map(x => x.atoms()).map(x => {
  return {
    source: node_ids[x[0]._id],
    target: node_ids[x[1]._id]
  }
})

const data = {
  nodes,
  links
}

// set the dimensions and margins of the graph
var margin = {top: 10, right: 30, bottom: 30, left: 40},
  width = 400 - margin.left - margin.right,
  height = 400 - margin.top - margin.bottom;

// append the svg object to the body of the page
var svg = d3.select("#my_dataviz")
.append("svg")
  .attr("width", width + margin.left + margin.right)
  .attr("height", height + margin.top + margin.bottom)
.append("g")
  .attr("transform",
        "translate(" + margin.left + "," + margin.top + ")");


  // Initialize the links
  var link = svg
    .selectAll("line")
    .data(data.links)
    .enter()
    .append("line")
      .style("stroke", "#aaa")    
      .attr("marker-end", "url(#triangle)");

  // Initialize the nodes
  var node = svg
    .selectAll("circle")
    .data(data.nodes)
    .enter()
    .append("circle")
      .attr("r", 20)
      .style("fill", "#69b3a2")
  
  
  var labels = svg
    .selectAll("text")
    .data(data.nodes)
    .enter()
    .append("text")
	    .text(function(d){return litToString(d.name, d.sign)})
  
  // Let's list the force we wanna apply on the network
  var simulation = d3.forceSimulation(data.nodes)                 // Force algorithm is applied to data.nodes
      .force("link", d3.forceLink()                               // This force provides links between nodes
            .id(function(d) { return d.id; })                     // This provide  the id of a node
            .links(data.links)                                    // and this the list of links
      )
      .force("charge", d3.forceManyBody().strength(-1000))         // This adds repulsion between nodes. Play with the -400 for the repulsion strength
      .force("center", d3.forceCenter(width / 2, height / 2))     // This force attracts nodes to the center of the svg area
      .on("end", ticked);

  // This function is run at each iteration of the force algorithm, updating the nodes position.
  function ticked() {
    link
        .attr("x1", function(d) { return d.source.x; })
        .attr("y1", function(d) { return d.source.y; })
        .attr("x2", function(d) { return d.target.x; })
        .attr("y2", function(d) { return d.target.y; });

    node
         .attr("cx", function (d) { return d.x; })
         .attr("cy", function(d) { return d.y; });
    
    labels
         .attr("dx", function (d) { return d.x-5; })
         .attr("dy", function(d) { return d.y+5; });
  }

