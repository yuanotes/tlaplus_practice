---- MODULE DirHard ----
EXTENDS Integers

VARIABLES small, big

TypeOK == /\ small \in  0..3
          /\ big \in 0..5

Init == /\ big  = 0
        /\ small = 0

FillSmall == /\ big' = big
             /\ small' = 3

FillBig == /\ small' = small
           /\ big' = 5

SmallToBig == IF big + small <= 5
                THEN /\ big' = big + small
                     /\ small' = 0
                ELSE /\ big' = 5
                     /\ small' = big + small - 5

BigToSmall == IF big + small <= 3
                THEN /\ small' = big + small
                     /\ big' = 0
                ELSE /\ small' = 3
                     /\ big' = small + big - 3

EmptyBig == /\ big' = 0
            /\ small' = small

EmptySmall == /\ small' = 0
              /\ big' = big


Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ SmallToBig
        \/ BigToSmall

Dest == big /= 4
====