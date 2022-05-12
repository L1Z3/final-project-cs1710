const d3 = require('d3')
d3.selectAll("svg > *").remove();
d3.select(svg).selectAll("*").remove();

const listOfNodes = Node.atoms(true);
const startNode = Traverse.atoms(true);
const edges = edges.atoms(true);

const xmap = new Map();
const ymap = new Map();

function randPosX(d) {
    pos = Math.floor(Math.random() * 500) + 25;
    xmap.set(d._id, pos);
    return pos;
}

function randPosY(d) {
    pos = Math.floor(Math.random() * 500) + 25;
    ymap.set(d._id, pos);
    return pos;
}

function color(d, i) {
    console.log(startNode)
    if (startNode._id.start._id == d._id) {
        return "#19eb0e";
    } else {
        return "#0495c2";
    }
}

d3.select(svg)
    .selectAll("nodes")
    .data(listOfNodes)
    .join("circle")
    .attr("cx", randPosX)
    .attr("cy", randPosY)
    .attr("r", 25)
    .style("fill", color)