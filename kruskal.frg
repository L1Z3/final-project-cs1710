#lang forge "final" "kg6EYhEuRtzmnKAu"

// option verbose 10

// stores info about Kruskal's explore progress
sig State {
    next: lone State,
    // set of edges that have been added to the tree in the current state
    treeEdges: set Node -> Int -> Node
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

/* This function creates a virtual "neighborsTreeEdges" field for the Node sig that stores 
   a set of nodes that a given node has as neighbors via treeEdges; enables syntax like "Node0.(neighborsTreeEdges[s])" */
fun neighborsTreeEdges(s: State): set Node -> Node {
    {n1: Node, n2: Node | some w: Int | n1 -> w -> n2 in s.treeEdges}
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

// makes a graph directed--no neighbor relationship is reciprocated
pred directed {
    all disj n1, n2: Node | n1 in n2.neighbors iff n2 not in n1.neighbors
}


// makes every weight positive
pred positiveWeights {
    all i: {i: Int | some n1, n2: Node | n1 -> i -> n2 in edges} | {
        i > 0
    }
}

pred wellformed {
    // at most one connection to any node
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
    // no edges have been added to the solution yet
    no s.treeEdges
}

pred canTransition[pre: State, post: State] {
    // post is pre's next
    pre.next = post

    // candidates is the set of edges that connect two non-reachable nodes
    let candidates = {n1: Node, i: Int, n2: Node | 
        (n1 -> i -> n2) in edges and not reachable[n2, n1, neighborsTreeEdges[pre]]} | 
    // the set of integers representing the edge weights of the candidates
    let candidateEdgeWeights = {i: Int | {some n1, n2: Node | n1 -> i -> n2 in candidates}} |
    // the minimum edge weight out of the candidate edge weights
    let minEdgeWeight = min[candidateEdgeWeights] |
    // the set of candidate edges that have the minimum weight
    let edgesWithMinWeight = {n1: Node, i: Int, n2: Node | (n1 -> i -> n2 in candidates) and i = minEdgeWeight} | {
        some disj n1, n2: Node | {
            // we assume undirectedness here
            (n1 -> minEdgeWeight -> n2) in edgesWithMinWeight
            pre.treeEdges + (n1 -> minEdgeWeight -> n2) 
                          + (n2 -> minEdgeWeight -> n1) 
                          = post.treeEdges
        }
    }
}

pred final[s: State] {
    // traversal ends when every node is reachable from some node
    some start: Node | all n: Node | n != start implies {
        reachable[n, start, neighborsTreeEdges[s]]
    }
}

pred doNothing[pre: State, post: State] {
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
    edges = `Node0 -> 4 -> `Node1
    next = `S0 -> `S1
}

// if doesn't follow shortest path, fails transitions
example chooseWrongPath is not {some pre, post: State | canTransition[pre, post]} for {
    State = `S0 + `S1
    Node = `Node0 + `Node1 + `Node2 + `Node3
    edges = `Node0 -> 1 -> `Node1 +
            `Node0 -> 7 -> `Node2 +
            `Node1 -> 1 -> `Node3 +
            `Node2 -> 7 -> `Node1 +
            `Node2 -> 7 -> `Node3
    next = `S0 -> `S1
    treeEdges = `S1 -> {`Node2 -> 7 -> `Node1}
}

// can complete a zigzag graph
example completesZigzag is TransitionStates for {
    State = `S0 + `S1 + `S2 + `S3
    Node = `Node0 + `Node1 + `Node2 + `Node3
    edges = `Node0 -> 4 -> `Node1 +
            `Node0 -> 8 -> `Node2 +
            `Node1 -> 8 -> `Node3 +
            `Node1 -> 1 -> `Node2 +
            `Node2 -> 1 -> `Node1 +
            `Node2 -> 3 -> `Node3
    next = `S0 -> `S1 +
        `S1 -> `S2 +
        `S2 -> `S3
    #Int = 5
}

// can complete wheel graph from center
example completesWheelFromCenter is TransitionStates for {
    State = `S0 + `S1 + `S2 + `S3 + `S4
    Node = `Node0 + `Node1 + `Node2 + `Node3 + `Node4
    edges = `Node0 -> 1 -> `Node1 +
            `Node0 -> 1 -> `Node2 +
            `Node0 -> 1 -> `Node3 +
            `Node0 -> 1 -> `Node4 +
            `Node1 -> 1 -> `Node2 +
            `Node2 -> 1 -> `Node3 +
            `Node3 -> 1 -> `Node4 +
            `Node4 -> 1 -> `Node1
    next = `S0 -> `S1 + 
    `S1 -> `S2 + 
    `S2 -> `S3 + 
    `S3 -> `S4
}

// can complete wheel graph from edge
example completesWheelFromEdge is TransitionStates for {
    State = `S0 + `S1 + `S2 + `S3 + `S4
    Node = `Node0 + `Node1 + `Node2 + `Node3 + `Node4
    edges = `Node0 -> 1 -> `Node1 +
            `Node0 -> 1 -> `Node2 +
            `Node0 -> 1 -> `Node3 +
            `Node0 -> 1 -> `Node4 +
            `Node1 -> 1 -> `Node2 +
            `Node2 -> 1 -> `Node3 +
            `Node3 -> 1 -> `Node4 +
            `Node4 -> 1 -> `Node1
    next = `S0 -> `S1 +
        `S1 -> `S2 +
        `S2 -> `S3 + 
        `S3 -> `S4
}

// no edges fails
example noEdges is not TransitionStates for {
    State = `S0
    Node = `Node0 + `Node1 + `Node2 + `Node3
}

// start state is final passes
example startingIsFinal is TransitionStates for {
    State = `S0
    Node = `Node0
}

// every node is connected
example allConnectedNodes is TransitionStates for {
    State = `S0 + `S1 + `S2
    Node = `Node0 + `Node1 + `Node2
    edges = `Node0 -> 1 -> `Node1 +
            `Node0 -> 1 -> `Node2 +
            `Node1 -> 1 -> `Node0 +
            `Node1 -> 1 -> `Node2 +
            `Node2 -> 1 -> `Node0 +
            `Node2 -> 1 -> `Node1
    next = `S0 -> `S1 +
        `S1 -> `S2
}

// negative weights passes
example negativeWeights is TransitionStates for {
    State = `S0 + `S1 + `S2
    Node = `Node0 + `Node1 + `Node2
    edges = `Node0 -> -1 -> `Node1 +
            `Node0 -> -1 -> `Node2 +
            `Node1 -> -1 -> `Node0 +
            `Node1 -> -1 -> `Node2 +
            `Node2 -> -1 -> `Node0 +
            `Node2 -> -1 -> `Node1
    next = `S0 -> `S1 +
        `S1 -> `S2
}

// disconnected node fails nice predicate
example disconnectedNode is not nice for {
    State = `S0 + `S1 + `S2 + `S3
    Node = `Node0 + `Node1 + `Node2 + `Node3 + `Node4
    edges = `Node0 -> 4 -> `Node1 +
            `Node0 -> 8 -> `Node2 +
            `Node1 -> 8 -> `Node3 +
            `Node1 -> 1 -> `Node2 +
            `Node2 -> 1 -> `Node1 +
            `Node2 -> 3 -> `Node3
    next = `S0 -> `S1 +
        `S1 -> `S2 +
        `S2 -> `S3
    #Int = 5
}

test expect {
    vacuous: {wellformed} is sat
    vacuousWithPrim: {
        wellformed
        TransitionStates
    } is sat
    directedFails: {
        wellformed
        TransitionStates
        directed
        some n: Node | all n2: Node | n2 != n implies {not edgeExists[n, n2] and not edgeExists[n2, n]}
        some f: State | {
            final[f] and {all n: Node | some n2: Node | some w: Int | n2 -> w -> n in f.treeEdges}
        }
    } is unsat
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
        positiveWeights
        // no incoming edges to some node that is the ending node
        some n: Node | {
            all n2: Node | n != n2 implies not edgeExists[n, n2] and not edgeExists[n2, n]
        }
        TransitionStates
        some f: State | {
            {all n: Node | some n2: Node | some w: Int | n2 -> w -> n in f.treeEdges}
        }
    } for {next is linear} is unsat
    numVisitedIncreasesByZeroOrOne: {
        wellformed
        positiveWeights
        TransitionStates
        not (all s1, s2: State | s1.next = s2 implies {
            #{s1.treeEdges} = #{s2.treeEdges} or
            (add[#{s1.treeEdges}, 2] = (#{s2.treeEdges}))
        })
    } for {next is linear} is unsat
    pathFoundIffReachable: {
        wellformed
        TransitionStates
        not(all disj n1, n2: Node | {
            reachable[n2, n1, neighbors] implies {
                some s: State | {
                    some n3: Node | some w: Int | n3 -> w -> n2 in s.treeEdges
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
    (#edges) < 30
    // temporary
    #{i: Int | {some n1, n2: Node | n1 -> i -> n2 in edges}} > 4
    // smallWeights
} for exactly 5 Node, exactly 6 Int, 15 State for {next is linear}
