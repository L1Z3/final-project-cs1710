const d3 = require('d3')
d3.selectAll("svg > *").remove();
d3.select(svg).selectAll("*").remove();

const listOfNodes = Node.atoms(true);
const states = State.atoms(true);

const xmap = new Map();
const ymap = new Map();

function randPosX(d) {
    pos = Math.floor(Math.random() * 350) + 120;
    xs = Array.from(xmap.values());
    for (let i = 0; i < xs.length; i++){
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
        while (Math.abs(pos - ys[i]) < 50){
            pos -= 10;
        }
    }
    ymap.set(d._id, pos);
    return pos;
}

function initPos() {
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
    return "#64bdd9";
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
            .attr("stroke","#abd2de")
            .attr("stroke-width",3)
            .attr('marker-end', 'url(#arrow)');
    }
    for (let i = 0; i < edges.length; i++){
        n1 = edges[i]._atoms[0]._id
        n2 = edges[i]._atoms[2]._id
        weight = edges[i]._atoms[1]._id
        avgx = (xmap.get(n1) + xmap.get(n2))/2 -11
        avgy = (ymap.get(n1) + ymap.get(n2))/2 -11
        d3.select(svg)
            .append("text")
            .attr("x", avgx)
            .attr("y", avgy)
            .attr("fill", "#023f52")
            .text(weight);
    }
}

switched = 0
function switchEdges() {
    if (switched == 0){
        switched = 1
        for (let i = 0; i < listOfNodes.length; i++){
            n = listOfNodes[i]
            nes = instance.atom(n._id).edges
            console.log(instance.atom(n._id).edges)
            for (let j = 0; j < nes._tuples.length; j++){
                ne = nes._tuples[j]
                len = ne._atoms[0]._id
                tgt = ne._atoms[1]._id
                nid = n._id
                console.log(nid)
                console.log(tgt)
                avgx = (xmap.get(nid) + xmap.get(tgt))/2 -11
                avgy = (ymap.get(nid) + ymap.get(tgt))/2 -11
                console.log(avgx)
                console.log(avgy)
                d3.select(svg)
                    .append("line")
                    .attr("x1",xmap.get(nid))  
                    .attr("y1",ymap.get(nid))  
                    .attr("x2",xmap.get(tgt))
                    .attr("y2",ymap.get(tgt))
                    .attr("stroke","black")
                    .attr("stroke-width",3)
                    .attr("stroke-dasharray", "4 8")
                    .attr('marker-end', 'url(#arrow)');
                d3.select(svg)
                    .append("line")
                    .attr("x1",xmap.get(nid))  
                    .attr("y1",ymap.get(nid))  
                    .attr("x2",xmap.get(tgt))
                    .attr("y2",ymap.get(tgt))
                    .attr("stroke","#bdbdbd")
                    .attr("stroke-width",2)
                    .attr("stroke-dasharray", "4 8")
                    .attr('marker-end', 'url(#arrow)');
                d3.select(svg)
                    .append("text")
                    .attr("x", avgx)
                    .attr("y", avgy)
                    .attr("fill", "#023f52")
                    .text(len);
                
            }
        }
        drawEdges()
    } else {
        switched = 0
        d3.select(svg).selectAll("*").remove();
        drawNodes()
        drawEdges()
        drawButtons()
    }
}

function outlines() {
    for (let i = 0; i < listOfNodes.length; i++){
            n = listOfNodes[i]
            nes = instance.atom(n._id).edges
            console.log(instance.atom(n._id).edges)
            for (let j = 0; j < nes._tuples.length; j++){
                ne = nes._tuples[j]
                len = ne._atoms[0]._id
                tgt = ne._atoms[1]._id
                nid = n._id
                console.log(nid)
                console.log(tgt)
                avgx = (xmap.get(nid) + xmap.get(tgt))/2 -11
                avgy = (ymap.get(nid) + ymap.get(tgt))/2 -11
                console.log(avgx)
                console.log(avgy)
                d3.select(svg)
                    .append("line")
                    .attr("x1",xmap.get(nid))  
                    .attr("y1",ymap.get(nid))  
                    .attr("x2",xmap.get(tgt))
                    .attr("y2",ymap.get(tgt))
                    .attr("stroke","black")
                    .attr("stroke-width",3)
                    .attr("stroke-dasharray", "4 8")
                    .attr('marker-end', 'url(#arrow)');
                d3.select(svg)
                    .append("line")
                    .attr("x1",xmap.get(nid))  
                    .attr("y1",ymap.get(nid))  
                    .attr("x2",xmap.get(tgt))
                    .attr("y2",ymap.get(tgt))
                    .attr("stroke","#bdbdbd")
                    .attr("stroke-width",2)
                    .attr("stroke-dasharray", "4 8")
                    .attr('marker-end', 'url(#arrow)');
                d3.select(svg)
                    .append("text")
                    .attr("x", avgx)
                    .attr("y", avgy)
                    .attr("fill", "#023f52")
                    .text(len);
                
            }
        }
}

curState = 0
function drawButtons() {
    d3.select(svg).append("rect")
        .attr("width", "90")
        .attr("height", "50")
        .attr("stroke", "black")
        .attr("fill", 'black')
        .attr("x", 50)
        .attr("y", 495)
        .attr("rx", 10)
        .attr("ry", 10)
        .on("click", switchEdges)
    d3.select(svg).append('text')
        .attr('x', 60)
        .attr('y', 525)
        .on("click", switchEdges)
        .attr("fill", "white")
        .attr("font-size", 9)
        .text('show/hide edges')
    d3.select(svg).append("rect")
        .attr("width", "90")
        .attr("height", "50")
        .attr("stroke", "black")
        .attr("fill", 'black')
        .attr("x", 150)
        .attr("y", 495)
        .attr("rx", 10)
        .attr("ry", 10)
        .on("click", prevState)
    d3.select(svg).append('text')
        .attr('x', 175)
        .attr('y', 525)
        .on("click", prevState)
        .attr("fill", "white")
        .text('prev')
    d3.select(svg).append("rect")
        .attr("width", "90")
        .attr("height", "50")
        .attr("stroke", "black")
        .attr("fill", 'black')
        .attr("x", 260)
        .attr("y", 495)
        .attr("rx", 10)
        .attr("ry", 10)
        .on("click", nextState)
    d3.select(svg).append('text')
        .attr('x', 285)
        .attr('y', 525)
        .on("click", nextState)
        .attr("fill", "white")
        .text('next')
    d3.select(svg).append('text')
        .attr('x', 375)
        .attr('y', 525)
        .attr("fill", "black")
        .text('State: ' + curState)
}
    

function prevState() {
    if (curState > 0) {
        curState -= 1
        d3.select(svg).selectAll("*").remove();
        
        drawNodes()
        if (switched == 1){
            outlines()
        }
        drawEdges()
        drawButtons()
    }
}

function nextState() {
    if (curState < states.length-1) {
        curState += 1
        d3.select(svg).selectAll("*").remove();
        
        drawNodes()
        if (switched == 1){
            outlines()
        }
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
drawNodes()
drawButtons()