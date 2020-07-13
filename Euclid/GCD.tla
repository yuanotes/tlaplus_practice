-------------------------------- MODULE GCD --------------------------------
EXTENDS Integers


Divides(p, n) ==              (**********************************)       
      \E q \in Int :          (* For integers p and n, equals   *)               
      n = q * p               (* TRUE iff p divides n -- which  *)
                              (* I think is really neat; don’t  *)
                              (* you?                           *)
                              (**********************************)

DivisorsOf(n) ==  {p \in Int: Divides(n, p)}

SetMax(S) == CHOOSE i \in S: \A j \in S: i >= j

GCD(m,n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))
=============================================================================
\* Modification History
\* Last modified Fri Jan 17 22:22:30 CST 2020 by chenyuan
\* Created Fri Jan 17 21:13:22 CST 2020 by chenyuan
