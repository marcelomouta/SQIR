Require Import UnitaryOps.
Local Open Scope ucom.

(* The unitary operator U(β) for the mixer Hamiltonian Hm
   n : number of qubits
   β : rotation angle parameter

   The operator is defined as:
    U(β) = e^(−i.β.Hm) = prodsum{j=1, n} e^(−i.β.σx_j)
   This is equivalent to applying Rx(2*β) on each qubit. *)
Fixpoint mixingUnitary (n : nat) (β : R) : base_ucom n :=
  match n with
    | 0    => SKIP
    | 1    => Rx (2*β) 0
    (* cast is required to match total circuit dimension *)
    | S n' => Rx (2*β) n' ; cast (mixingUnitary n' β) n
  end.


Definition graph := list (nat * nat). (* Is an adjacency list enough? *)
(* Other graph implementations in Coq:
   - https://github.com/coq-contribs/graph-basics
   - https://gist.github.com/andrejbauer/8dade8489dff8819c352e88f446154a1
   - https://stackoverflow.com/questions/24753975/simple-graph-theory-proofs-using-coq
   - https://softwarefoundations.cis.upenn.edu/vfa-current/Color.html#lab294 *)




