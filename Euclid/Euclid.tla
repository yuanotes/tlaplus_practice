------------------------------- MODULE Euclid -------------------------------
EXTENDS Integers, GCD

CONSTANTS M, N

ASSUME {M, N} \in Nat \ {0}

(***************************************************************************
--algorithm Euclid {
variables x = M, y = N;
{ while ( x /= y ) {
  if (x < y) { y := y - x}
  else { x := x - y}
 };
}
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES x, y, pc

vars == << x, y, pc >>

Init == (* Global variables *)
        /\ x = M
        /\ y = N
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF x /= y
               THEN /\ IF x < y
                          THEN /\ y' = y - x
                               /\ x' = x
                          ELSE /\ x' = x - y
                               /\ y' = y
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << x, y >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sat Jan 18 14:52:50 CST 2020 by chenyuan
\* Created Sat Jan 18 14:42:51 CST 2020 by chenyuan
