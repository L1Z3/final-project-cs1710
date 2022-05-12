# CS1710 Final Project

## Discussion of Model

**What tradeoffs did you make in choosing your representation? What else did you try that didn’t work as well?**

One of the main decisions we needed to make in choosing how to represent our model was whether to use pure Forge or to also encorporate Electrum mode. Due to the relative ease in writing examples in pure Forge and fact that we had no real use for lassos, we elected to go with pure Forge instead of incorporating Electrum mode. 

Additionally, we tried out a few different ways of representing a) our graphs and b) the actual traversal data of our algorithms, but eventually we settled on our current representation, mostly due to the simplicity of writing it this way, but also for other miscellaneous reasons--for instance, the way we implement edges is largely ordered the way it is so that, given a theme in Sterling, the graphs actually look like proper graphs and the edges that Dijkstra's/Prim's/Kruskal's find actually look like they are traversing the graph.

Another tradeoff that came up quite a lot was how exactly to implement constraints that deal with the number of edges. For instance, for a long while we had a `wellformed` constraint that ensured that there was at most one directed edge from any particular node to another by counting the number of integers that exist in an edge between those two nodes. However, this allowed for situations where the number of edges between those two nodes was equal to the number of integers that existed, causing an overflow issue no matter the bitwidth. Thus, in overcoming these sorts of overflow issues, we encountered tradeoffs between ease of implementation and proper handling of such edge cases. 


**What assumptions did you make about scope? What are the limits of your model?**

One of the primary limits of our model is the size of the graph. Ideally, in order for the run to finish in a reasonable amount of time, we cap the number of nodes at around 5. The most nodes we have run our model with is around 8-9. 

Other than that, the main limiting factor in generalizing our model is runtime. As the size of graphs increase, the runtime of our model increases dramatically, meaning that to show any properties that only manifest in more complex graphs would be essentially impossible given our current implementation. 


**Did your goals change at all from your proposal? Did you realize anything you planned was unrealistic, or that anything you thought was unrealistic was doable?**

Our goals going into the project were somewhat optimistic (overachiever instincts) and so we somewhat significantly scaled back our scope from what we originally intended. At our first design check, Carter recommended that we scale back the number of algorithms that we were examining and thus we did so and thus only focused on Dijkstra's, Prim's, and Kruskal's instead of also looking into other algorithms. Additionally, we did not do any of the items in our reach goal.

Some other ideas that we had that we didn't get to include were allowing for all three algorithms to run in lock-step and implementing a PBT-like verification algorithm for all algorithms (see bottom of README for more info as to how this would have worked). We decided these were also out of the scope of what we had time for for this project.


**How should we understand an instance of your model and what your custom visualization shows?**

An instance of our model corresponds to one graph that the model generates and a run of Dijkstra's/Prim's/Kruskal's for that map--that is, in the case of Dijkstra's, it will show the steps it takes to find the shortest path between the chosen start and end nodes; and in the case of Prim's and Kruskal's, it will show the steps taken to find the minimum spanning tree. 

For Dijkstra's, the theme provided shows the graph and the path associated with each node at each state. For Prim's and Kruskal's, our custom visualization shows both the input graph as well as the edges the algorithm has found so far at each step. 


## Demonstration Video

[Link to demo video](https://drive.google.com/file/d/12ZFP2CRMRloHwalJuHF4D6tOewOUZ_H5/view?usp=sharing)

## Other Notes

After running Dijkstra's apply the file "theme_dijkstra_v1.json" to see the model in action. For Prim's and Kruskal's, you can either apply the themes or the visualization script, though in most cases the visualization script creates a better experience.

**More info about our PBT idea:**

For Dijsktra's, we thought of having tests that would ensure:
* All nodes and edges in the input graph are also in the outputed path.
* The path has the correct starting location.
* The path is actually a connected path in the input graph.
* Verify that at each step, there is no shorter path to each node using the method discussed [here](http://tinyurl.com/verify-shortest-paths).

For Prim's and Kruskal's, we thought of having tests that would ensure:
* The output is actually a tree (#edges = #nodes - 1)
* Verify every edge on the output tree is actually on the input graph.
* Verify the outputted tree spans the graph.
* Verify that Prim's and Kruskal's both give the same edge weight for a given graph.

We have a partial solution for verifying that the output of Prim's and Kruskal's is actually a tree, but the test verifying that the output is always a tree runs very very slowly and thus is commented out. (It does pass though!)
