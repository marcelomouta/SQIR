Require Import UnitaryOps.
Local Open Scope ucom.

Definition bell : base_ucom 2 := H 0; CNOT 0 1.

(* Definition bell_state : Matrix (2^2) (1^2) :=
1 / √2 .* ( ∣ 0,0 ⟩ .+ ∣ 1,1 ⟩). *)

Lemma bell_correct: uc_eval bell × ∣ 0,0 ⟩ = 1 / √2 .* ( ∣ 0,0 ⟩ .+ ∣ 1,1 ⟩).
Proof.
  simpl.
  autorewrite with eval_db; simpl.
  solve_matrix.
Qed.