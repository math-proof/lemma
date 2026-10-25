/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Complexity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.TuringMachines.Part4
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.TuringMachines
import Def.v1.Atlas.TheoryOfComputation.code.NondeterministicTM
import Notation.v1.Atlas.TheoryOfComputation.code.Reductions
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Notation.v1.Atlas.TheoryOfComputation.code.Complexity


namespace TuringMachine

open TuringMachine

variable {Q : Type} {Γ : Type} [DecidableEq Q]

/-- The complexity class coNP: `A ∈ coNP` iff `Aᶜ ∈ NP`. -/
def InCoNP {Γ : Type} (A : Set (List Γ)) : Prop :=
  InNP Aᶜ

/-- Sequential composition of TMs: run `F` to completion, then transfer control
to `M_B`, finally collapsing `M_B`'s accept/reject states to fresh accept/reject
states of the composed machine. Used to reduce one decision problem to another. -/
noncomputable def composedTM
    {Γ : Type} {Q_F Q_B : Type} [DecidableEq Q_F] [DecidableEq Q_B]
    (F : TM Q_F Γ) (M_B : TM Q_B Γ) : TM ((Q_F ⊕ Q_B) ⊕ Fin 2) Γ where
  blank := F.blank
  inputAlpha := F.inputAlpha
  blank_not_in_inputAlpha := F.blank_not_in_inputAlpha
  δ := fun q γ => match q with
    | .inl (.inl q_F) =>
      if q_F = F.qAccept ∨ q_F = F.qReject then
        (.inl (.inr M_B.q₀), γ, Direction.R)
      else
        let (q', b, d) := F.δ q_F γ
        (.inl (.inl q'), b, d)
    | .inl (.inr q_B) =>
      if q_B = M_B.qAccept then
        (.inr ⟨0, by omega⟩, γ, Direction.R)
      else if q_B = M_B.qReject then
        (.inr ⟨1, by omega⟩, γ, Direction.R)
      else
        let (q', b, d) := M_B.δ q_B γ
        (.inl (.inr q'), b, d)
    | .inr n => (.inr n, γ, Direction.R)
  q₀ := .inl (.inl F.q₀)
  qAccept := .inr ⟨0, by omega⟩
  qReject := .inr ⟨1, by omega⟩
  qReject_ne_qAccept := by simp


/-- If `f` is polynomial-time computable and `B ∈ P`, then `{w | f w ∈ B} ∈ P`.
This is the key technical lemma behind `A ≤ₚ B ∧ B ∈ P → A ∈ P`. -/
protected def IsNPHard {Γ : Type} (B : Set (List Γ)) : Prop :=
  ∀ A : Set (List Γ), InNP A → PolyReducible A B

/-- `B` is NP-complete: `B ∈ NP` and `B` is NP-hard. -/
protected def IsNPComplete {Γ : Type} (B : Set (List Γ)) : Prop :=
  InNP B ∧ TuringMachine.IsNPHard B

end TuringMachine
