Require Import UnitaryOps.
Require Import QuantumLib.DiscreteProb.
Local Open Scope ucom.

(* A graph is simply an adjacency list dependent on the number of vertices (order) of the graph *)
Definition graph (order : nat) := list (nat * nat).
(* Alternative graph implementation in Coq:
    https://github.com/coq-contribs/graph-basics
Require Import GraphBasics.Graphs. *)

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
   g : problem graph
   n : number of qubits
   γ : rotation angle parameter

   The operator is defined as:
    U(γ) = e^(−i.γ.Hc) = prodsum{edges} e^(−i.γ.C_jk)
   where C_jk = 1/2 (−σz_j.σz_k + 1)
*)
Fixpoint cost_unitary {n : nat} (g : graph n) (γ : R) : base_ucom n :=
  match g with
  | [] => SKIP
  | (j,k) :: g' => CNOT j k ; Rz (2*γ) k ; CNOT j k ; cost_unitary g' γ
  end.

(* The initial state of QAOA is the uniform superposition over computational basis states.
   n : number of qubits *)
Definition initial_state n : base_ucom n := npar n U_H.

(* Use vectors to bind number of parameters to p?
    https://coq.inria.fr/library/Coq.Vectors.VectorDef.html 
Require Import Vector.
Import VectorNotations.
Fixpoint QAOA_layers {n p : nat} (g : graph) (betas gammas : t R p) : base_ucom n :=
  match p with
  | 0    => SKIP
  | S p' => let (be, betas') := uncons (betas : t R (S p')) in 
            let (ga, gammas') := uncons gammas in
              cost_unitary g ga ; mixing_unitary be ; QAOA_layers g tl betas  gammas'
  end.

Fixpoint QAOA_layers {n p : nat} (g : graph) (betas gammas : t R p) : base_ucom n :=
  match betas, gammas with
  | β :: betas', γ :: gammas' => cost_unitary g γ ; mixing_unitary β ; QAOA_layers g betas' gammas'
  | _, _ => SKIP
  end. *)
Fixpoint QAOA_layers {n : nat} (g : graph n) (p : nat) (betas gammas : list R) : base_ucom n :=
  match (betas, gammas, p) with
  | (β :: betas', γ :: gammas', S p') => cost_unitary g γ ; mixing_unitary β ;
                                         QAOA_layers g p' betas' gammas'
  | _ => SKIP
  end.

Definition QAOA_circuit {n : nat} (g : graph n) (p : nat) (betas gammas : list R) : base_ucom n :=
  initial_state n; QAOA_layers g p betas gammas.


(* Do we need to calculate cut size? 
   Qiskit implementation does it for the expected value used in optimization
   Qimaera uses it to deliver best cut of all runs 
Fixpoint cut_size {n : nat} (g: graph n) (c : cut) : nat :=
  match g with
  | [] => 0
  | (j,k) :: g' => if negb (eqb (c j) (c k)) 
                    then S (@cut_size n g' c)
                    else (@cut_size n g' c)
  end. *)

(* For simplicity, we do not provide an optimizer in this implementation *)
Definition classical_optimization {n : nat} (g : graph n) (betas gammas : list R)
                                                                          : list R * list R :=
(* Is it better to assume there is an external optimizer instead of providing dummy function? *)
  (betas,gammas).

(* Returns index of measuread qubit state after running circuit *)
Definition run {n : nat} (c : base_ucom n) (rnd : R) : nat :=
  sample (apply_u (uc_eval c)) rnd.

Definition QAOA_body {n : nat} (g : graph n) (p : nat) (betas gammas : list R) (rnd : R) : option cut :=
  let (betas', gammas') := classical_optimization g betas gammas in
  let result := run (QAOA_circuit g p betas' gammas') rnd in
  (* Convert sampled state to boolean function *)
  Some (nat_to_funbool n result).


Definition QAOA {n : nat} (g : graph n) (p: nat) (betas gammas : list R) (rnds : list R) : option cut :=
  iterate rnds (QAOA_body g p betas gammas).