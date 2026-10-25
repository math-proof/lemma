/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/TMComposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.TuringMachines.Part4
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.TuringMachines


namespace TuringMachine

variable {Q₁ Q₂ Γ : Type} [DecidableEq Q₁] [DecidableEq Q₂]

/--
Sequential composition of two Turing machines `M₁` and `M₂` sharing the same
tape alphabet `Γ`. The composite machine runs `M₁` first; whenever `M₁` would
halt (accept or reject) it transitions to `M₂.q₀` instead and continues with
`M₂`. The composite then accepts iff `M₂` accepts and rejects iff `M₂` rejects.
The state space `(Q₁ ⊕ Q₂) ⊕ Fin 2` keeps each machine's states in its own
copy and uses the final `Fin 2` for the new accept/reject states.
-/
noncomputable def TM.sequentialCompose
    (M₁ : TM Q₁ Γ) (M₂ : TM Q₂ Γ) : TM ((Q₁ ⊕ Q₂) ⊕ Fin 2) Γ where
  blank := M₁.blank
  inputAlpha := M₁.inputAlpha
  blank_not_in_inputAlpha := M₁.blank_not_in_inputAlpha
  δ := fun q γ => match q with
    | .inl (.inl q₁) =>
      if q₁ = M₁.qAccept ∨ q₁ = M₁.qReject then
        (.inl (.inr M₂.q₀), γ, Direction.R)
      else
        let (q', b, d) := M₁.δ q₁ γ
        (.inl (.inl q'), b, d)
    | .inl (.inr q₂) =>
      if q₂ = M₂.qAccept then
        (.inr ⟨0, by omega⟩, γ, Direction.R)
      else if q₂ = M₂.qReject then
        (.inr ⟨1, by omega⟩, γ, Direction.R)
      else
        let (q', b, d) := M₂.δ q₂ γ
        (.inl (.inr q'), b, d)
    | .inr n => (.inr n, γ, Direction.R)
  q₀ := .inl (.inl M₁.q₀)
  qAccept := .inr ⟨0, by omega⟩
  qReject := .inr ⟨1, by omega⟩
  qReject_ne_qAccept := by simp

/--
The starting configuration of `M₂` in the composite execution: take the
configuration `M₁` reaches after `n₁` steps on input `w`, move the head one cell
right, and set the state to `M₂.q₀`.
-/
noncomputable def phase2InitConfig
    (M₁ : TM Q₁ Γ) (M₂ : TM Q₂ Γ) (w : List Γ) (n₁ : ℕ) : Config Q₂ Γ :=
  let c₁ := M₁.runOnInput w n₁
  ⟨M₂.q₀, c₁.headPos + 1, c₁.tape⟩

end TuringMachine
