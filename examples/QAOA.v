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
(* Alternative graph implementation in Coq:
   - https://github.com/coq-contribs/graph-basics *)

(* The unitary operator U(γ) for the cost Hamiltonian Hc 
   g : problem graph
   n : number of qubits
   γ : rotation angle parameter

   The operator is defined as:
    U(γ) = e^(−i.γ.Hc) = prodsum{edges} e^(−i.γ.C_jk)
   where C_jk = 1/2 (−σz_j.σz_k + 1)
*)
Fixpoint costUnitary (g : graph) (n : nat) (γ : R) : base_ucom n := (* should we tie n to number of vertices in g? *)
  match g with
  | [] => SKIP
  | (j,k) :: g' => CNOT j k ; Rz (2*γ) k ; CNOT j k ;
                  costUnitary g' n γ
  end.