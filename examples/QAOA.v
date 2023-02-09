Require Import Vector.
Require Import UnitaryOps.
Require Import GraphBasics.Graphs.
Require Import QuantumLib.DiscreteProb.
Local Open Scope ucom.

(* A Cut is a boolean funtion that maps a vertex index to the corresponding set *)
Definition cut := nat -> bool.

(* The unitary operator U(β) for the mixer Hamiltonian Hm
   n : number of qubits
   β : rotation angle parameter

   The operator is defined as:
    U(β) = e^(−i.β.Hm) = prodsum{j=1, n} e^(−i.β.σx_j)
   This is equivalent to applying Rx(2*β) on each qubit. *)
Fixpoint mixing_unitary {n : nat} (β : R) : base_ucom n :=
  match n with
  | 0    => SKIP
  (* cast is required to match total circuit dimension *)
  | S n' => Rx (2*β) n' ; cast (@mixing_unitary n' β) n
  end.

(* The unitary operator U(γ) for the problem Hamiltonian Hc 
   edges : list of graph edges
   n : number of qubits
   γ : rotation angle parameter

   The operator is defined as:
    U(γ) = e^(−i.γ.Hc) = prodsum{edges} e^(−i.γ.C_jk)
   where C_jk = 1/2 (−σz_j.σz_k + 1)
*)
Fixpoint cost_unitary {n : nat} (edges : E_list) (γ : R) : base_ucom n :=
  match edges with
  | [] => SKIP
  | E_ends (index j) (index k) :: edges' => CNOT j k ; Rz (2*γ) k ; CNOT j k ; cost_unitary edges' γ
  end.

(* The initial state of QAOA is the uniform superposition over computational basis states.
   n : number of qubits *)
Definition initial_state n : base_ucom n := npar n U_H.

Import VectorNotations.
(* See convoy pattern: http://adam.chlipala.net/cpdt/html/MoreDep.html *)
Fixpoint QAOA_layers {p : nat} {v a} (g : Graph v a) (betas gammas: Vector.t R p) : base_ucom (G_order g) :=
  match betas in Vector.t _ n return Vector.t _ n -> base_ucom (G_order g) with
  | β :: betas' => fun gs => cost_unitary (GE_list g) (Vector.hd gs) ; mixing_unitary β ; QAOA_layers g betas' (Vector.tl gs)
  | _ => fun gs => SKIP
  end gammas.

Definition QAOA_circuit {v a} (g : Graph v a) (p : nat) (betas gammas : Vector.t R p) : base_ucom (G_order g) :=
  initial_state (G_order g); QAOA_layers g betas gammas.


(* Do we need to calculate cut size? 
   Qiskit implementation does it for the expected value used in optimization
   Qimaera uses it to deliver best cut of all runs 
Fixpoint cut_size (edges: E_list) (c : cut) : nat :=
  match edges with
  | [] => 0
  | E_ends (index j) (index k) :: edges' => if negb (eqb (c j) (c k)) 
                    then S (@cut_size edges' c)
                    else (@cut_size edges' c)
  end. *)

(* For simplicity, we do not provide an optimizer in this implementation *)
Definition classical_optimization {v a p} (g : Graph v a) (betas gammas : Vector.t R p)
                                                                          : Vector.t R p * Vector.t R p :=
(* Is it better to assume there is an external optimizer instead of providing dummy function? *)
  (betas,gammas).

(* Returns index of measuread qubit state after running circuit *)
Definition run {n : nat} (c : base_ucom n) (rnd : R) : nat :=
  sample (apply_u (uc_eval c)) rnd.

Definition QAOA_body {v a} (g : Graph v a) (p : nat) (betas gammas : Vector.t R p) (rnd : R) : option cut :=
  let (betas', gammas') := classical_optimization g betas gammas in
  let result := run (QAOA_circuit g p betas' gammas') rnd in
  (* Convert sampled state to boolean function *)
  Some (nat_to_funbool (G_order g) result).


Definition QAOA {v a} (g : Graph v a) (p: nat) (betas gammas : Vector.t R p) (rnds : list R) : option cut :=
  iterate rnds (QAOA_body g p betas gammas).