------------------------------ MODULE traffic ------------------------------
Color == {"red", "green"}

NextColor(c) == CASE c = "red" -> "green"
                  [] c = "green" -> "red"
                  
(*--algorithm traffic
variables
  at_light = TRUE,
  light = "red";


fair+ process light_proc = "light_proc"
begin
  Cycle:
    while at_light do
      light := NextColor(light);
    end while;
end process;



fair+ process car_proc = "car_proc"
begin
  Drive:
    when light = "green";
    at_light := FALSE;
end process;



end algorithm;*)
\* BEGIN TRANSLATION
VARIABLES at_light, light, pc

vars == << at_light, light, pc >>

ProcSet == {"light_proc"} \cup {"car_proc"}

Init == (* Global variables *)
        /\ at_light = TRUE
        /\ light = "red"
        /\ pc = [self \in ProcSet |-> CASE self = "light_proc" -> "Cycle"
                                        [] self = "car_proc" -> "Drive"]

Cycle == /\ pc["light_proc"] = "Cycle"
         /\ IF at_light
               THEN /\ light' = NextColor(light)
                    /\ pc' = [pc EXCEPT !["light_proc"] = "Cycle"]
               ELSE /\ pc' = [pc EXCEPT !["light_proc"] = "Done"]
                    /\ light' = light
         /\ UNCHANGED at_light

light_proc == Cycle

Drive == /\ pc["car_proc"] = "Drive"
         /\ light = "green"
         /\ at_light' = FALSE
         /\ pc' = [pc EXCEPT !["car_proc"] = "Done"]
         /\ light' = light

car_proc == Drive

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == light_proc \/ car_proc
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ SF_vars(light_proc)
        /\ SF_vars(car_proc)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue May 26 23:43:27 CST 2020 by chenyuan
\* Created Mon May 25 22:33:59 CST 2020 by chenyuan
