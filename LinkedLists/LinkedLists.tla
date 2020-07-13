---------------------------- MODULE LinkedLists ----------------------------

CONSTANT NULL


LOCAL INSTANCE FiniteSets \* For Cardinality

LOCAL INSTANCE Sequences \* For len

LOCAL INSTANCE Integers \* For ..

LOCAL INSTANCE TLC  \* For assert

LOCAL PointerMaps(Nodes) == [Nodes -> Nodes \union {NULL}]
    

LOCAL Range(f) == { f[x]: x \in DOMAIN f }

Ring(LL) == (DOMAIN LL = Range(LL))

First(LL) ==
    IF Ring(LL)
    THEN CHOOSE node \in DOMAIN LL:
        TRUE
    ELSE CHOOSE node \in DOMAIN LL:
        node \notin Range(LL)
        
Cyclic(LL) == NULL \notin Range(LL)
    
\* PointerMap is an element of PointerMaps
LOCAL isLinkedList(PointerMap) ==
    LET
        nodes == DOMAIN PointerMap
        all_seqs == [1..Cardinality(nodes) -> nodes]
    IN \E ordering \in all_seqs:
        \* each node points to the next node in the ordering
        /\ \A i \in 1..Len(ordering) - 1:
            PointerMap[ordering[i]] = ordering[i+1]
        \* all nodes in the mapping appear in the ordering
        /\ nodes \subseteq Range(ordering)
        
        
LinkedLists(Nodes) ==
    IF NULL \in Nodes THEN Assert(FALSE, "NULL cannot be in Nodes")
    ELSE
    LET
        node_subsets == (SUBSET Nodes \ {{}})
        
        pointer_map_sets == { PointerMaps(subn) : subn \in node_subsets }
        
        all_pointer_maps == UNION pointer_map_sets
    IN  
        { pm \in all_pointer_maps : isLinkedList(pm) }

=============================================================================
\* Modification History
\* Last modified Mon Jul 13 21:55:02 CST 2020 by chenyuan
\* Created Wed Jun 10 23:45:09 CST 2020 by chenyuan
