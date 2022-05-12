const d3 = require('d3')
d3.selectAll("svg > *").remove();
d3.select(svg).selectAll("*").remove();

const listOfNodes = Node.atoms(true);
const startNode = instance.atom('Traverse0').start
const states = State.atoms(true);

const xmap = new Map();
const ymap = new Map();

function randPosX(d) {
    pos = Math.floor(Math.random() * 350) + 120;
    xs = Array.from(xmap.values());
    for (let i = 0; i < xs.length; i++){
        console.log(Math.abs(pos - xs[i]))
        while (Math.abs(pos - xs[i]) < 50){
            pos -= 10;
        }
    }
    xmap.set(d._id, pos);
    return pos;
}

function randPosY(d) {
    pos = Math.floor(Math.random() * 350) + 120;
    ys = Array.from(ymap.values());
    for (let i = 0; i < ys.length; i++){
        console.log(Math.abs(pos - ys[i]))
        while (Math.abs(pos - ys[i]) < 50){
            pos -= 10;
        }
    }
    ymap.set(d._id, pos);
    return pos;
}

function initPos() {
    console.log(listOfNodes)
    for (let i = 0; i < listOfNodes.length; i++){
        randPosX(listOfNodes[i])
        randPosY(listOfNodes[i])
    }
}

function getxPos(d) {
    return xmap.get(d._id)
}

function getyPos(d) {
    return ymap.get(d._id)
}

function color(d) {
    if (startNode._id == d._id) {
        return "#19eb0e";
    } else {
        return "#0495c2";
    }
}

function drawEdges() {
    s4e = instance.atom('State' + curState).treeEdges
    edges = s4e._tuples
    for (let i = 0; i < edges.length; i++){
        n1 = edges[i]._atoms[0]._id
        n2 = edges[i]._atoms[2]._id
        weight = edges[i]._atoms[1]._id
        d3.select(svg)
            .append("line")
            .attr("x1",xmap.get(n1))  
            .attr("y1",ymap.get(n1))  
            .attr("x2",xmap.get(n2))
            .attr("y2",ymap.get(n2))
            .attr("stroke","#0495c2")
            .attr("stroke-width",3)
            .attr('marker-end', 'url(#arrow)');
        avgx = (xmap.get(n1) + xmap.get(n2))/2 -10
        avgy = (ymap.get(n1) + ymap.get(n2))/2 -10
        d3.select(svg)
            .append("text")
            .attr("x", avgx)
            .attr("y", avgy)
            .attr("fill", "#023f52")
            .text(weight);
    }
}

curState = 0
function drawButtons() {
    //previous button

    d3.select(svg).append("rect")
        .attr("width", "100")
        .attr("height", "50")
        .attr("stroke", "black")
        .attr("fill", 'white')
        .attr("x", 100)
        .attr("y", 500)
        .on("click", prev)
    d3.select(svg).append('text')
        .attr('x', 125)
        .attr('y', 530)
        .on("click", prev)
        .text('prev')
    //current step display
    d3.select(svg).append('text')
        .attr('x', 250)
        .attr('y', 530)
        .text('Current Step: ' + curState)
    //next button
    d3.select(svg).append("rect")
        .attr("width", "100")
        .attr("height", "50")
        .attr("stroke", "black")
        .attr("fill", 'white')
        .attr("x", 400)
        .attr("y", 500)
        .on("click", next)
    d3.select(svg).append('text')
        .attr('x', 425)
        .attr('y', 530)
        .on("click", next)
        .text('next')
    }

function prev() {
    if (curState > 0) {
        curState -= 1
        d3.select(svg).selectAll("*").remove();
        drawNodes()
        drawEdges()
        drawButtons()
    }
}

function next() {
    console.log(states)
    if (curState < states.length-1) {
        curState += 1
        d3.select(svg).selectAll("*").remove();
        drawNodes()
        drawEdges()
        drawButtons()
    }
}

function drawNodes() {
    d3.select(svg)
        .selectAll("nodes")
        .data(listOfNodes)
        .join("circle")
        .attr("cx", getxPos)
        .attr("cy", getyPos)
        .attr("r", 25)
        .style("fill", color);
}

initPos()
drawButtons()