-------------------------------- MODULE main --------------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets

CONSTANTS Nodes, NULL

INSTANCE LinkedLists WITH NULL <- NULL

AllLinkedLists == LinkedLists(Nodes)

CycleImpliesTowParants(ll) ==
    Cyclic(ll) <=>
      \/ Ring(ll)
      \/ \E n \in DOMAIN ll:
            Cardinality({p \in DOMAIN ll: ll[p] = n}) = 2

Valid ==
    /\ \A ll \in AllLinkedLists:
        /\ Assert(CycleImpliesTowParants(ll), <<"Counterexample:", ll>>)


=============================================================================
\* Modification History
\* Last modified Mon Jul 13 22:08:14 CST 2020 by chenyuan
\* Created Wed Jun 10 23:44:32 CST 2020 by chenyuan
