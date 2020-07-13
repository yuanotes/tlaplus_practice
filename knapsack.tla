------------------------------ MODULE knapsack ------------------------------

EXTENDS TLC, Integers, Sequences

PT == INSTANCE PT

Capacity == 4

Items == { "a", "b", "c"}

HardcodedItemSet == [
    a |-> [size |-> 1, value |-> 1 ],
    b |-> [size |-> 2, value |-> 3 ],
    c |-> [size |-> 3, value |-> 1]]

ItemParams == [size: 2..4, value: 0..5]

ItemSets == [Items -> ItemParams]

KnapsackSize(sack, itemset) == 
    LET size_for(item) == itemset[item].size * sack[item]
    IN PT!ReduceSet(LAMBDA item, acc: size_for(item) + acc, Items, 0)
    
ValidKnapsacks(itemset) == { sack \in [Items -> 0..4]: KnapsackSize(sack, itemset) <= Capacity}


\* A minor acmount of duplicate code

KnapsackValue(sack, itemset) ==
    LET value_for(item) == itemset[item].value * sack[item]
    IN PT!ReduceSet(LAMBDA item, acc: value_for(item) + acc, Items, 0)
    
BestKnapsack(itemset) ==
    LET all == ValidKnapsacks(itemset)
    IN CHOOSE best \in all:
        \A worse \in all \ {best}: KnapsackValue(best, itemset) > KnapsackValue(worse, itemset)

BestKnapsacksOne(itemset) ==
    LET all == ValidKnapsacks(itemset)
    IN
        CHOOSE all_the_best \in SUBSET all:
           /\ \E good \in all_the_best:
                /\ \A other \in all_the_best:
                    KnapsackValue(good, itemset) = KnapsackValue(other, itemset)
                /\ \A worse \in all \ all_the_best:
                    KnapsackValue(good, itemset) > KnapsackValue(worse, itemset)
                    
BestKnapsacksTwo(itemset) ==
    LET all == ValidKnapsacks(itemset)
        best == CHOOSE best \in all:
            \A worse \in all \ {best}:
                KnapsackValue(best, itemset) >= KnapsackValue(worse, itemset)
        value_of_best == KnapsackValue(best, itemset)
    IN
        {k \in all: value_of_best = KnapsackValue(k, itemset)}
        
BestKnapsacks(itemset) ==
    LET value(sack) == KnapsackValue(sack, itemset)
        all == ValidKnapsacks(itemset)
        best == CHOOSE best \in all:
            \A worse \in all \ {best}:
                value(best) >= value(worse)
    IN
        {k \in all: value(best) = value(k)}        
 
(*--algorithm debug
variables itemset \in ItemSets
begin
    assert BestKnapsack(itemset) \in ValidKnapsacks(itemset);
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES itemset, pc

vars == << itemset, pc >>

Init == (* Global variables *)
        /\ itemset \in ItemSets
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(BestKnapsack(itemset) \in ValidKnapsacks(itemset), 
                   "Failure of assertion at line 60, column 5.")
         /\ pc' = "Done"
         /\ UNCHANGED itemset

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Wed May 20 22:59:20 CST 2020 by chenyuan
\* Created Tue May 19 22:23:15 CST 2020 by chenyuan
