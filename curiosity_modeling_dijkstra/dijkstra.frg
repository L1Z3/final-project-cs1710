#lang forge "cm" "kg6EYhEuRtzmnKAu"

// option verbose 10

// stores info about Dijkstra's explore progress
sig State {
    next: lone State,
    /* A function from a node to a *sequence* of nodes; represents the shortest path
       that Dijkstra's has found from the start to this node at a given state;
       the sequence is none when a node has not yet been explored */
    paths: pfunc Node -> Int -> Node,
    /* each node has a total current path length at a given state; this is none
       when a node has not yet been explored */
    pathLengths: pfunc Node -> Int
}

// stores info about the starting node for Dijkstra's and the goal node
one sig Traverse {
    start : one Node,
    end : one Node
}

// the nodes of the graph
sig Node {
    /* a set of int, node pairs representing all outgoing edges from the current node;
       the int is the weight of that edge and the node is the node that this edges connects
       the current node to */
    edges: set Int -> Node
}

/* This function creates a virtual "visited" field for the State sig that stores all
   the nodes that have been visited at a given state. It pulls its info from whether
   or the pathLength for a node exists at a given state. This enables syntax like "State0.visited" */
fun visited: set State -> Node {
    {s: State, n: Node | #{i : Int | n -> i in pathLengths[s]} > 0}
}

/* This function creates a virtual "neighbors" field for the Node sig that stores 
   a set of nodes that a given node has as neighbors; enables syntax like "Node0.neighbors" */
fun neighbors: set Node -> Node {
    {n1, n2: Node | some w: Int | n1 -> w -> n2 in edges}
}

// get the weight of the edge going from n1 to n2
fun getEdgeWeight(n1: Node, n2: Node): lone Int {
    {i: Int | n1 -> i -> n2 in edges}
}

// enforces a connected graph; every node is reachable from every other node
pred connected {
    all disj n1, n2 : Node | reachable[n1, n2, neighbors]
}

// makes directed graphs a bit more interesting: no two nodes each connect to each other
pred noMutualEdges {
    all n1, n2 : Node | {
        n2 in n1.neighbors implies not n1 in n2.neighbors
    }
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
    (all n1, n2: Node | {
        // WARNING: OVERFLOW CAN HAPPEN, ENSURE BITWIDTH IS GOOD
        let numEdgesFromN1ToN2 = #{i: Int | n1 -> i -> n2 in edges} | {
            numEdgesFromN1ToN2 = 0 or numEdgesFromN1ToN2 = 1
        }
    })
    // enforce that each path is a sequence
    all s: State, n: Node | {
        isSeqOf[s.paths[n], Node]
    }
}

// determines whether there is an edge from n1 to n2
pred edgeExists[n1: Node, n2: Node] {
    some {i: Int | n1 -> i -> n2 in edges}
}


pred init[s: State] {
    // set up non-start Node values
    all n : Node | (n != Traverse.start) implies {
        // the path sequence for all nodes except the start is empty
        isEmpty[s.paths[n]]
        no s.pathLengths[n]
    }

    // starting path is initialized to 0, with only itself as path
    let startPathSeq = s.paths[Traverse.start] | {
        // the only element in the start's path is the starting element
        elems[startPathSeq] = Traverse.start
        #inds[startPathSeq] = 1
        s.pathLengths[Traverse.start] = 0
    }
}

pred canTransition[pre: State, post: State] {
    // post is pre's next
    pre.next = post

    // candidates is the set of edges that connect a node inside the visited set to a node outside the visited set
    let candidates = {n1: Node, i: Int, n2: Node | (n1 in pre.visited) and (n2 not in pre.visited) and (n1 -> i -> n2 in edges)} | 
    // the set of proposed new path lengths; that is, all the lengths that a candidate node could have 
    //      if an edge were added to it from inside the visited set
    let newPathLengths = {i: Int | {
        // find some pair of nodes that are in the candidates set
        some n1, n2: Node | some {i: Int | n1 -> i -> n2 in candidates} and {
            // the new pathLength for n2 would be the pathLength of n1 + the weight of that edge
            let newLen = add[pre.pathLengths[n1], getEdgeWeight[n1, n2]] | {
                newLen = i
            }
        }
    }} |
    let minNewPathLength = min[newPathLengths] |
    let edgesCreatingMinPath = {n1: Node, i: Int, n2: Node | (n1 -> i -> n2 in candidates) and add[pre.pathLengths[n1], getEdgeWeight[n1, n2]] = minNewPathLength} |
    let newNodes = edgesCreatingMinPath[Node][Int] | {
        some newNode: Node | newNode in newNodes and {
            // pathLengths and paths remain unchanged for nodes that are not newNode
            all n: Node | n != newNode implies {
                pre.pathLengths[n] = post.pathLengths[n]
                pre.paths[n] = post.paths[n]
            }
            post.pathLengths[newNode] = minNewPathLength
            let oldNode = {n: Node | some i: Int | n -> i -> newNode in edgesCreatingMinPath} | 
            let newPath = post.paths[newNode] |
            let oldPath = pre.paths[oldNode] | {
                newPath = oldPath + ((#inds[oldPath]) -> newNode)
            }
        }
    }
}

pred final[s: State] {
    // end is in visited set
    Traverse.end in s.visited

    all pre: State | reachable[s, pre, next] implies not (Traverse.end in pre.visited)
}

pred doNothing[pre: State, post: State] {
    all n: Node | {
        pre.pathLengths[n] = post.pathLengths[n]
        pre.paths[n] = post.paths[n]
    }
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

// equivalent of final, but for Explore
pred finalExplore[s: State] {
    all n: Node | reachable[n, Traverse.start, neighbors] implies {
        n in s.visited
    }

    all pre: State | reachable[s, pre, next] implies not {
        all n: Node | reachable[n, Traverse.start, neighbors] implies {
            n in pre.visited
        }
    }
}

// an alternative to TransitionStates that just explores until it has found everything it can, not stopping at Traverse.end
pred Explore {
    some initState, finalState: State {
        -- no state has init as its next state, fulfills init requirements
        no prev: State | prev.next = initState
        init[initState]

        // final[finalState]
        finalExplore[finalState]
        -- if final has future states, they are do nothing
        all post1, post2: State | {
            (reachable[post2, finalState, next] and post2 = post1.next) implies {doNothing[post1, post2]}
        }
        
        -- link init to final state via next
        reachable[finalState, initState, next]

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


// Example blocks
// check a sample transition
example validTransition is {some pre, post: State | canTransition[pre, post]} for {
    State = `S0 + `S1
    Node = `Node0 + `Node1
    Traverse = `Traverse0
    edges = `Node0 -> 4 -> `Node1
    start = `Traverse0 -> `Node0
    end = `Traverse0 -> `Node1
    next = `S0 -> `S1
    paths = `S0 -> `Node0 -> 0 -> `Node0 +
            `S1 -> `Node0 -> 0 -> `Node0 +
            `S1 -> `Node1 -> 0 -> `Node0 +
            `S1 -> `Node1 -> 1 -> `Node1
    pathLengths = `S0 -> `Node0 -> 0+
                `S1 -> `Node0 -> 0 +
                `S1 -> `Node1 -> 4
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
    end = `Traverse0 -> `Node3
    next = `S0 -> `S1
    paths = `S0 -> `Node0 -> 0 -> `Node0 +
            `S1 -> `Node0 -> 0 -> `Node0 +
            `S1 -> `Node2 -> 0 -> `Node0 +
            `S1 -> `Node2 -> 1 -> `Node2
    pathLengths = `S0 -> `Node0 -> 0 +
                `S1 -> `Node0 -> 0 +
                `S1 -> `Node2 -> 7
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
    end = `Traverse0 -> `Node3
    next = `S0 -> `S1 +
        `S1 -> `S2 +
        `S2 -> `S3
    paths = `S0 -> `Node0 -> 0 -> `Node0 +
            `S1 -> `Node0 -> 0 -> `Node0 +
            `S1 -> `Node1 -> 0 -> `Node0 +
            `S1 -> `Node1 -> 1 -> `Node1 +
            `S2 -> `Node0 -> 0 -> `Node0 +
            `S2 -> `Node1 -> 0 -> `Node0 +
            `S2 -> `Node1 -> 1 -> `Node1 +
            `S2 -> `Node2 -> 0 -> `Node0 +
            `S2 -> `Node2 -> 1 -> `Node1 +
            `S2 -> `Node2 -> 2 -> `Node2 +
            `S3 -> `Node0 -> 0 -> `Node0 +
            `S3 -> `Node1 -> 0 -> `Node0 +
            `S3 -> `Node1 -> 1 -> `Node1 +
            `S3 -> `Node2 -> 0 -> `Node0 +
            `S3 -> `Node2 -> 1 -> `Node1 +
            `S3 -> `Node2 -> 2 -> `Node2 +
            `S3 -> `Node3 -> 0 -> `Node0 +
            `S3 -> `Node3 -> 1 -> `Node1 +
            `S3 -> `Node3 -> 2 -> `Node2 +
            `S3 -> `Node3 -> 3 -> `Node3

    pathLengths = `S0 -> `Node0 -> 0 +
                `S1 -> `Node0 -> 0 +
                `S1 -> `Node1 -> 4 + 
                `S2 -> `Node0 -> 0 +
                `S2 -> `Node1 -> 4 +
                `S2 -> `Node2 -> 5 +
                `S3 -> `Node0 -> 0 +
                `S3 -> `Node1 -> 4 +
                `S3 -> `Node2 -> 5 +
                `S3 -> `Node3 -> 8
    #Int = 5
}


// can complete wheel graph from center
example completesWheelFromCenter is TransitionStates for {
    State = `S0 + `S1
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
    end = `Traverse0 -> `Node1
    next = `S0 -> `S1
    paths = `S0 -> `Node0 -> 0 -> `Node0 +
            `S1 -> `Node0 -> 0 -> `Node0 +
            `S1 -> `Node1 -> 0 -> `Node0 +
            `S1 -> `Node1 -> 1 -> `Node1

    pathLengths = `S0 -> `Node0 -> 0+
                `S1 -> `Node0 -> 0 +
                `S1 -> `Node1 -> 1 
}

// can complete wheel graph from edge
example completesWheelFromEdge is TransitionStates and Explore for {
    State = `S0 + `S1 + `S2 + `S3
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
    end = `Traverse0 -> `Node4
    next = `S0 -> `S1 +
        `S1 -> `S2 +
        `S2 -> `S3
    paths = `S0 -> `Node1 -> 0 -> `Node1 +
            `S1 -> `Node1 -> 0 -> `Node1 +
            `S1 -> `Node2 -> 0 -> `Node1 +
            `S1 -> `Node2 -> 1 -> `Node2 +
            `S2 -> `Node1 -> 0 -> `Node1 +
            `S2 -> `Node2 -> 0 -> `Node1 +
            `S2 -> `Node2 -> 1 -> `Node2 +
            `S2 -> `Node3 -> 0 -> `Node1 +
            `S2 -> `Node3 -> 1 -> `Node2 +
            `S2 -> `Node3 -> 2 -> `Node3 +
            `S3 -> `Node1 -> 0 -> `Node1 +
            `S3 -> `Node2 -> 0 -> `Node1 +
            `S3 -> `Node2 -> 1 -> `Node2 +
            `S3 -> `Node3 -> 0 -> `Node1 +
            `S3 -> `Node3 -> 1 -> `Node2 +
            `S3 -> `Node3 -> 2 -> `Node3 +
            `S3 -> `Node4 -> 0 -> `Node1 +
            `S3 -> `Node4 -> 1 -> `Node2 +
            `S3 -> `Node4 -> 2 -> `Node3 +
            `S3 -> `Node4 -> 3 -> `Node4
    pathLengths = `S0 -> `Node1 -> 0 +
                `S1 -> `Node1 -> 0 +
                `S1 -> `Node2 -> 1 +
                `S2 -> `Node1 -> 0 +
                `S2 -> `Node2 -> 1 +
                `S2 -> `Node3 -> 2 +
                `S3 -> `Node1 -> 0 +
                `S3 -> `Node2 -> 1 +
                `S3 -> `Node3 -> 2 +
                `S3 -> `Node4 -> 3
    #Int = 5
}

// Starting state is final state passes
example startingIsFinal is TransitionStates for {
    State = `S0 + `S1
    next = `S0 -> `S1
    Node = `Node0 + `Node1 + `Node2 + `Node3
    Traverse = `Traverse0
    start = `Traverse0 -> `Node0
    end = `Traverse0 -> `Node0
    edges = `Node0 -> 1 -> `Node1 +
            `Node1 -> 1 -> `Node2 +
            `Node2 -> 1 -> `Node3
    paths = `S0 -> `Node0 -> 0 -> `Node0 +
            `S1 -> `Node0 -> 0 -> `Node0 
    pathLengths = `S0 -> `Node0 -> 0 +
                `S1 -> `Node0 -> 0 
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
    end = `Traverse0 -> `Node2
    next = `S0 -> `S1 +
        `S1 -> `S2
    paths = `S0 -> `Node0 -> 0 -> `Node0 +
            `S1 -> `Node0 -> 0 -> `Node0 +
            `S1 -> `Node1 -> 0 -> `Node0 +
            `S1 -> `Node1 -> 1 -> `Node1 +
            `S2 -> `Node0 -> 0 -> `Node0 +
            `S2 -> `Node1 -> 0 -> `Node0 +
            `S2 -> `Node1 -> 1 -> `Node1 +
            `S2 -> `Node2 -> 0 -> `Node0 +
            `S2 -> `Node2 -> 1 -> `Node2
    pathLengths = `S0 -> `Node0 -> 0 +
                `S1 -> `Node0 -> 0 +
                `S1 -> `Node1 -> 1 +
                `S2 -> `Node0 -> 0 +
                `S2 -> `Node1 -> 1 +
                `S2 -> `Node2 -> 1
}

// negative weights fails
example negativeWeights is not TransitionStates for {
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
    end = `Traverse0 -> `Node2
    next = `S0 -> `S1 +
        `S1 -> `S2
    paths = `S0 -> `Node0 -> 0 -> `Node0 +
            `S1 -> `Node0 -> 0 -> `Node0 +
            `S1 -> `Node1 -> 0 -> `Node0 +
            `S1 -> `Node1 -> 1 -> `Node1 +
            `S2 -> `Node0 -> 0 -> `Node0 +
            `S2 -> `Node1 -> 0 -> `Node0 +
            `S2 -> `Node1 -> 1 -> `Node1 +
            `S2 -> `Node2 -> 0 -> `Node0 +
            `S2 -> `Node2 -> 1 -> `Node2
    pathLengths = `S0 -> `Node0 -> 0 +
                `S1 -> `Node0 -> 0 +
                `S1 -> `Node1 -> -1 +
                `S2 -> `Node0 -> 0 +
                `S2 -> `Node1 -> -1 +
                `S2 -> `Node2 -> -1
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
    end = `Traverse0 -> `Node3
    next = `S0 -> `S1 +
        `S1 -> `S2 +
        `S2 -> `S3
    paths = `S0 -> `Node0 -> 0 -> `Node0 +
            `S1 -> `Node0 -> 0 -> `Node0 +
            `S1 -> `Node1 -> 0 -> `Node0 +
            `S1 -> `Node1 -> 1 -> `Node1 +
            `S2 -> `Node0 -> 0 -> `Node0 +
            `S2 -> `Node1 -> 0 -> `Node0 +
            `S2 -> `Node1 -> 1 -> `Node1 +
            `S2 -> `Node2 -> 0 -> `Node0 +
            `S2 -> `Node2 -> 1 -> `Node1 +
            `S2 -> `Node2 -> 2 -> `Node2 +
            `S3 -> `Node0 -> 0 -> `Node0 +
            `S3 -> `Node1 -> 0 -> `Node0 +
            `S3 -> `Node1 -> 1 -> `Node1 +
            `S3 -> `Node2 -> 0 -> `Node0 +
            `S3 -> `Node2 -> 1 -> `Node1 +
            `S3 -> `Node2 -> 2 -> `Node2 +
            `S3 -> `Node3 -> 0 -> `Node0 +
            `S3 -> `Node3 -> 1 -> `Node1 +
            `S3 -> `Node3 -> 2 -> `Node2 +
            `S3 -> `Node3 -> 3 -> `Node3

    pathLengths = `S0 -> `Node0 -> 0 +
                `S1 -> `Node0 -> 0 +
                `S1 -> `Node1 -> 4 + 
                `S2 -> `Node0 -> 0 +
                `S2 -> `Node1 -> 4 +
                `S2 -> `Node2 -> 5 +
                `S3 -> `Node0 -> 0 +
                `S3 -> `Node1 -> 4 +
                `S3 -> `Node2 -> 5 +
                `S3 -> `Node3 -> 8
    #Int = 5
}

test expect {
    vacuous: {wellformed} is sat
    vacuousWithDijkstra: {
        wellformed
        TransitionStates
    } is sat
    travelToDisconnectedImpossible: {
        wellformed
        positiveWeights
        // no incoming edges to some node that is the ending node
        some n: Node | {
            all n2: Node | n != n2 implies not edgeExists[n2, n]
            Traverse.end = n
            Traverse.start != n
        }
        TransitionStates
    } for {next is linear} is unsat
    numVisitedIncreasesByZeroOrOne: {
        wellformed
        positiveWeights
        TransitionStates
        not (all s1, s2: State | s1.next = s2 implies {
            ((#(s1.visited)) = (#(s2.visited))) or
            (add[(#(s1.visited)), 1] = (#(s2.visited)))
        })
    } for {next is linear} is unsat
    // if a connected graph is explored, it will find every node every time
    connectedAlwaysHasSolution: {
        wellformed
        connected
        not(Explore implies {
            some s: State | {   
                s.visited = Node
            }
        })
    } for {next is linear} is unsat
    pathFoundIffReachable: {
        wellformed
        Explore
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
    wellformed
    nice
    TransitionStates
    (#edges) < 15
    smallWeights
} for exactly 5 Node, exactly 5 Int, exactly 5 State for {next is linear}
