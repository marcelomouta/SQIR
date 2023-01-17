Require Import UnitaryOps.
Local Open Scope ucom.

(* The mixing unitary operator U(β)
   n : number of qubits
   β : rotation angle parameter

   The operator is defined as:
    U(β) = prodsum{j=1, n} e^(−i.β.σx_j)
   This is equivalent to applying Rx(2*β) on each qubit. *)
Fixpoint mixingUnitary (n : nat) (β : R) : base_ucom n :=
  match n with
    | 0    => SKIP
    | 1    => Rx (2*β) 0
    (* cast is required to match total circuit dimension *)
    | S n' => Rx (2*β) n' ; cast (mixingUnitary n' β) n
  end.
