#lang forge "final" "kg6EYhEuRtzmnKAu"

// option verbose 10

// stores info about Prim's explore progress
sig State {
    next: lone State,
    // nodes that have been visited in the current state
    visited: set Node,
    // set of edges that have been added to the tree in the current state
    // for some reason this displays as a bidirectional arrow in Sterling, which is good.
    treeEdges: set Node -> Int -> Node
}

// stores info about the starting node for Prim's
one sig Traverse {
    start : one Node
}


// the nodes of the graph
sig Node {
    /* a set of int, node pairs representing all outgoing edges from the current node;
       the int is the weight of that edge and the node is the node that this edges connects
       the current node to */
    edges: set Int -> Node
}

/* This function creates a virtual "neighbors" field for the Node sig that stores 
   a set of nodes that a given node has as neighbors; enables syntax like "Node0.neighbors" */
fun neighbors: set Node -> Node {
    {n1, n2: Node | some w: Int | n1 -> w -> n2 in edges}
}

fun treeNeighbors[s: State]: set Node -> Node {
    {n1, n2: Node | some w: Int | n1 -> w -> n2 in s.treeEdges}
}

// get the weight of the edge going from n1 to n2
fun getEdgeWeight(n1: Node, n2: Node): lone Int {
    {i: Int | n1 -> i -> n2 in edges}
}

// enforces a connected graph; every node is reachable from every other node
pred connected {
    all disj n1, n2 : Node | reachable[n1, n2, neighbors]
}


// makes a graph undirected--every neighbor relationship is reciprocated
pred undirected {
    all n1, n2 : Node | {
        getEdgeWeight[n1, n2] = getEdgeWeight[n2, n1]
    }
}

// makes nodes unable to be their own neighbor
pred noSelfNeighbor {
    all n1: Node | not n1 in n1.neighbors
}

// special case of directed--no neighbor relationship is reciprocated
pred directed {
    all disj n1, n2: Node | n1 in n2.neighbors iff n2 not in n1.neighbors
}

// makes the graph a tree
pred tree {
    // there is one node such that every other node is reachable from that node
    one n: Node | {
        all n2: Node | n != n2 implies {
            reachable[n2, n, neighbors]
            // each node that's not the top of the tree has some parent
            one n3: Node | {
                n2 in n3.neighbors
            }
            // no node connects to the top
            n not in n2.neighbors
        }
    }
    noSelfNeighbor
}

// makes every weight positive
pred positiveWeights {
    all i: {i: Int | some n1, n2: Node | n1 -> i -> n2 in edges} | {
        i > 0
    }
}

pred wellformed {
    // at most one connection to any node
    // (all n1, n2: Node | {
    //     // WARNING: OVERFLOW CAN HAPPEN, ENSURE BITWIDTH IS GOOD
    //     let numEdgesFromN1ToN2 = #{i: Int | n1 -> i -> n2 in edges} | {
    //         numEdgesFromN1ToN2 = 0 or numEdgesFromN1ToN2 = 1
    //     }
    // })
    all n1, n2: Node | {
        lone i: Int | {
            n1 -> i -> n2 in edges
        }
    }
}

// determines whether there is an edge from n1 to n2
pred edgeExists[n1: Node, n2: Node] {
    some {i: Int | n1 -> i -> n2 in edges}
}


pred init[s: State] {
    // only the starting node has been visited in the starting state
    s.visited = Traverse.start

    // no edges have been added to the solution yet
    no s.treeEdges
}

pred canTransition[pre: State, post: State] {
    // post is pre's next
    pre.next = post

    // candidates is the set of edges that connect a node inside the visited set to a node outside the visited set
    let candidates = {n1: Node, i: Int, n2: Node | (n1 in pre.visited) and (n2 not in pre.visited) and (n1 -> i -> n2 in edges)} | 
    // the set of integers representing the edge weights of the candidates
    let candidateEdgeWeights = {i: Int | {some n1, n2: Node | n1 -> i -> n2 in candidates}} |
    // the minimum edge weight out of the candidate edge weights
    let minEdgeWeight = min[candidateEdgeWeights] |
    // the set of candidate edges that have the minimum weight
    let edgesWithMinWeight = {n1: Node, i: Int, n2: Node | (n1 -> i -> n2 in candidates) and i = minEdgeWeight} |
    let newNodes = edgesWithMinWeight[Node][Int] | {
        some newNode: Node | newNode in newNodes and {
            pre.visited + newNode = post.visited
            some oldNode: Node | oldNode in {n: Node | some i: Int | n -> i -> newNode in edgesWithMinWeight} and {
                pre.treeEdges + (oldNode -> getEdgeWeight[oldNode, newNode] -> newNode) 
                              + (newNode -> getEdgeWeight[newNode, oldNode] -> oldNode) 
                              = post.treeEdges
            }
        }
    }
}

pred final[s: State] {
    // traversal ends when every node is in the graph
    all n: Node | reachable[n, Traverse.start, neighbors] implies {
        n in s.visited
    }
}

pred doNothing[pre: State, post: State] {
    pre.visited = post.visited
    pre.treeEdges = post.treeEdges
}

pred TransitionStates {
    some initState, finalState: State {
        -- no state has init as its next state, fulfills init requirements
        no prev: State | prev.next = initState
        init[initState]

        final[finalState]
        -- if final has future states, they are do nothing
        all post1, post2: State | {
            (reachable[post2, finalState, next] and post2 = post1.next) implies {doNothing[post1, post2]}
        }
        
        -- link init to final state via next
        not final[initState] implies reachable[finalState, initState, next]

        -- valid transitions before final state
        all s: State | {(s != finalState and not reachable[s, finalState, next]) implies canTransition[s, s.next]}
    }
}
    
pred nice {
    connected
    noSelfNeighbor
    positiveWeights
}

pred smallWeights {
    all n1, n2: Node | {
        let weight = getEdgeWeight[n1, n2] | {
            some weight implies weight < 5
        }
    }
}

pred treeEdgesIsTree[s: State] { 
    // the number of edges is one less than the number of nodes 
    let nodesInTreeEdges = {n: Node | n in (s.treeEdges).Node.Int or n in Int.(Node.(s.treeEdges))} | { 
        (#(s.treeEdges) = subtract[multiply[#nodesInTreeEdges, 2], 2]) or 
        (#s.treeEdges = 0 and #nodesInTreeEdges = 0)
    } 
} 

// Example blocks
// check a sample transition
example validTransition is {some pre, post: State | canTransition[pre, post]} for {
    State = `S0 + `S1
    Node = `Node0 + `Node1
    Traverse = `Traverse0
    edges = `Node0 -> 4 -> `Node1
    start = `Traverse0 -> `Node0
    next = `S0 -> `S1
}

// if doesn't follow shortest path, fails transitions
example chooseWrongPath is not {some pre, post: State | canTransition[pre, post]} for {
    State = `S0 + `S1
    Node = `Node0 + `Node1 + `Node2 + `Node3
    Traverse = `Traverse0
    edges = `Node0 -> 1 -> `Node1 +
            `Node0 -> 7 -> `Node2 +
            `Node1 -> 1 -> `Node3 +
            `Node2 -> 7 -> `Node1 +
            `Node2 -> 7 -> `Node3
    start = `Traverse0 -> `Node0
    next = `S0 -> `S1
    treeEdges = `S1 -> {`Node2 -> 7 -> `Node1}
}

// can complete a zigzag graph
example completesZigzag is TransitionStates for {
    State = `S0 + `S1 + `S2 + `S3
    Node = `Node0 + `Node1 + `Node2 + `Node3
    Traverse = `Traverse0
    edges = `Node0 -> 4 -> `Node1 +
            `Node0 -> 8 -> `Node2 +
            `Node1 -> 8 -> `Node3 +
            `Node1 -> 1 -> `Node2 +
            `Node2 -> 1 -> `Node1 +
            `Node2 -> 3 -> `Node3
    start = `Traverse0 -> `Node0
    next = `S0 -> `S1 +
        `S1 -> `S2 +
        `S2 -> `S3
    #Int = 5
}

// can complete wheel graph from center
example completesWheelFromCenter is TransitionStates for {
    State = `S0 + `S1 + `S2 + `S3 + `S4
    Node = `Node0 + `Node1 + `Node2 + `Node3 + `Node4
    Traverse = `Traverse0
    edges = `Node0 -> 1 -> `Node1 +
            `Node0 -> 1 -> `Node2 +
            `Node0 -> 1 -> `Node3 +
            `Node0 -> 1 -> `Node4 +
            `Node1 -> 1 -> `Node2 +
            `Node2 -> 1 -> `Node3 +
            `Node3 -> 1 -> `Node4 +
            `Node4 -> 1 -> `Node1
    start = `Traverse0 -> `Node0
    next = `S0 -> `S1 + 
    `S1 -> `S2 + 
    `S2 -> `S3 + 
    `S3 -> `S4
}

// can complete wheel graph from edge
example completesWheelFromEdge is TransitionStates for {
    State = `S0 + `S1 + `S2 + `S3 + `S4
    Node = `Node0 + `Node1 + `Node2 + `Node3 + `Node4
    Traverse = `Traverse0
    edges = `Node0 -> 1 -> `Node1 +
            `Node0 -> 1 -> `Node2 +
            `Node0 -> 1 -> `Node3 +
            `Node0 -> 1 -> `Node4 +
            `Node1 -> 1 -> `Node2 +
            `Node2 -> 1 -> `Node3 +
            `Node3 -> 1 -> `Node4 +
            `Node4 -> 1 -> `Node1
    start = `Traverse0 -> `Node1
    next = `S0 -> `S1 +
        `S1 -> `S2 +
        `S2 -> `S3 + 
        `S3 -> `S4
}

// Starting state is final state passes
example startingIsFinal is TransitionStates for {
    State = `S0
    Node = `Node0 + `Node1 + `Node2 + `Node3
    Traverse = `Traverse0
    start = `Traverse0 -> `Node0
}

// every node is connected
example allConnectedNodes is TransitionStates for {
    State = `S0 + `S1 + `S2
    Node = `Node0 + `Node1 + `Node2
    Traverse = `Traverse0
    edges = `Node0 -> 1 -> `Node1 +
            `Node0 -> 1 -> `Node2 +
            `Node1 -> 1 -> `Node0 +
            `Node1 -> 1 -> `Node2 +
            `Node2 -> 1 -> `Node0 +
            `Node2 -> 1 -> `Node1
    start = `Traverse0 -> `Node0
    next = `S0 -> `S1 +
        `S1 -> `S2
}

// negative weights passes
example negativeWeights is TransitionStates for {
    State = `S0 + `S1 + `S2
    Node = `Node0 + `Node1 + `Node2
    Traverse = `Traverse0
    edges = `Node0 -> -1 -> `Node1 +
            `Node0 -> -1 -> `Node2 +
            `Node1 -> -1 -> `Node0 +
            `Node1 -> -1 -> `Node2 +
            `Node2 -> -1 -> `Node0 +
            `Node2 -> -1 -> `Node1
    start = `Traverse0 -> `Node0
    next = `S0 -> `S1 +
        `S1 -> `S2
}

// disconnected node fails nice predicate
example disconnectedNode is not nice for {
    State = `S0 + `S1 + `S2 + `S3
    Node = `Node0 + `Node1 + `Node2 + `Node3 + `Node4
    Traverse = `Traverse0
    edges = `Node0 -> 4 -> `Node1 +
            `Node0 -> 8 -> `Node2 +
            `Node1 -> 8 -> `Node3 +
            `Node1 -> 1 -> `Node2 +
            `Node2 -> 1 -> `Node1 +
            `Node2 -> 3 -> `Node3
    start = `Traverse0 -> `Node0
    next = `S0 -> `S1 +
        `S1 -> `S2 +
        `S2 -> `S3
    #Int = 5
}


test expect {
    vacuous: {wellformed} is sat
    vacuousWithPrim: {
        wellformed
        undirected
        TransitionStates
    } is sat
    directedFails: {
        wellformed
        TransitionStates
        directed
        some n: Node | not reachable[n, Traverse.start, neighbors] and Traverse.start != n
        some f: State | {
            final[f] and {all n: Node | n in f.visited}
        }
    } for {next is linear} is unsat
    // this test below passes and ensures that all solutions are indeed trees, but takes a very long time to run- commented out for the sake of runtime
    /*treeEdgesIsTreeTest: {
        (wellformed and
        undirected and
        TransitionStates) implies
        {all s: State | final[s] implies {
            treeEdgesIsTree[s]
        }}
    } for {next is linear} is theorem*/
    travelToDisconnectedImpossible: {
        wellformed
        undirected
        // no incoming edges to some node that is the ending node
        some n: Node | {
            all n2: Node | n != n2 implies not edgeExists[n, n2] and not edgeExists[n2, n]
            Traverse.start != n
        }
        TransitionStates
        some f: State | {
            all n: Node | n in f.visited
        }
    } for {next is linear} is unsat
    numVisitedIncreasesByZeroOrOne: {
        wellformed
        undirected
        TransitionStates
        not (all s1, s2: State | s1.next = s2 implies {
            ((#(s1.visited)) = (#(s2.visited))) or
            (add[(#(s1.visited)), 1] = (#(s2.visited)))
        })
    } for {next is linear} is unsat
    pathFoundIffReachable: {
        wellformed
        undirected
        TransitionStates
        not(all n: Node | {
            // a path will be found if and only if the node is the start or it's reachable
            (reachable[n, Traverse.start, neighbors] or n = Traverse.start) iff {
                some s: State | {
                    n in s.visited
                }
            }
        })
    } for {next is linear} is unsat
}


run {
    undirected
    wellformed
    nice
    TransitionStates
    (#edges) < 20
    // temporary
    // #{i: Int | {some n1, n2: Node | n1 -> i -> n2 in edges}} = 6
    // smallWeights
} for exactly 5 Node, exactly 5 Int, exactly 5 State for {next is linear}