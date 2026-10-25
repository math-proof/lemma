/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BuildingsFromBNPairs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.BNPair.Basic.Part2
import Def.v1.Atlas.Buildings.code.BNPair.ParabolicDefs.Part2
import Lemma.Nat.NonemptyBruhatCell
import Lemma.Set.All_In_StandardParabolic
import Lemma.Nat.B.le.Closure_BruhatCell
import Theorem.v1.Atlas.Buildings.code.BNPair.ConjugatorProof
import Def.v1.Atlas.Buildings.code.BNPair.NormalizerParabolicProof
import Mathlib.Tactic.Group
import Theorem.v1.Atlas.Buildings.code.BNPair.BuildingsFromBNPairs.Part5
set_option linter.unusedSectionVars false

variable {B_idx : Type*} [DecidableEq B_idx]


namespace BNPair

variable {G : Type*} [Group G] {M : CoxeterMatrix B_idx}

/-- Forward map of the poset isomorphism: a special subset $X = g P_{S'}$ is sent to the
proper parabolic $g P_{S'} g^{-1}$. -/
noncomputable def conjugationForward (bp : BNPair G M)
    (X : bp.specialSubsets) : bp.properParabolics :=
  ⟨bp.conjugateParabolic (bp.specialSubsetReprG X) (bp.specialSubsetReprS X),
   ⟨bp.specialSubsetReprG X, bp.specialSubsetReprS X, bp.specialSubsetRepr_ne_univ X, rfl⟩⟩

/-- Inverse map of the poset isomorphism: a proper parabolic $Q = g P_{S'} g^{-1}$ is sent
back to the coset $g P_{S'}$. -/
noncomputable def conjugationBackward (bp : BNPair G M)
    (Q : bp.properParabolics) : bp.specialSubsets :=
  ⟨bp.leftCoset (bp.properParabolicReprG Q) (bp.properParabolicReprS Q),
   ⟨bp.properParabolicReprG Q, bp.properParabolicReprS Q, bp.properParabolicRepr_ne_univ Q, rfl⟩⟩

/-- Order isomorphism $\text{specialSubsets} \;\simeq_o\; \text{properParabolics}$
realized by conjugation. The two maps are mutual inverses, and inclusion of cosets
corresponds to inclusion of conjugate parabolics. -/
noncomputable def poset_orderIso_specialSubsets_properParabolics (bp : BNPair G M)
    (bd : BruhatProperties bp) (ax : BNPairAxioms bp) :
    bp.specialSubsets ≃o bp.properParabolics where
  toFun := conjugationForward bp
  invFun := conjugationBackward bp
  left_inv := by
    intro X
    ext : 1


    show (conjugationBackward bp (conjugationForward bp X) : Set G) = (X : Set G)
    simp only [conjugationForward, conjugationBackward]

    set g₁ := bp.specialSubsetReprG X
    set S₁ := bp.specialSubsetReprS X
    set Q_val := bp.conjugateParabolic g₁ S₁
    set Q_mem : Q_val ∈ bp.properParabolics :=
      ⟨g₁, S₁, bp.specialSubsetRepr_ne_univ X, rfl⟩
    set Q : bp.properParabolics := ⟨Q_val, Q_mem⟩
    set g₂ := bp.properParabolicReprG Q
    set S₂ := bp.properParabolicReprS Q
    have heq_Q : Q_val = bp.conjugateParabolic g₂ S₂ := properParabolicRepr_eq bp Q


    have h_inj := conjugation_injective_on_cosets bp bd ax g₂ g₁ S₂ S₁ heq_Q.symm
    rw [h_inj]
    exact (specialSubsetRepr_eq bp X).symm
  right_inv := by
    intro Q
    ext : 1
    show (conjugationForward bp (conjugationBackward bp Q) : Set G) = (Q : Set G)
    simp only [conjugationBackward, conjugationForward]
    set g₁ := bp.properParabolicReprG Q
    set S₁ := bp.properParabolicReprS Q
    set X_val := bp.leftCoset g₁ S₁
    set X_mem : X_val ∈ bp.specialSubsets :=
      ⟨g₁, S₁, bp.properParabolicRepr_ne_univ Q, rfl⟩
    set X : bp.specialSubsets := ⟨X_val, X_mem⟩
    set g₂ := bp.specialSubsetReprG X
    set S₂ := bp.specialSubsetReprS X
    have heq_X : X_val = bp.leftCoset g₂ S₂ := specialSubsetRepr_eq bp X


    have hS_eq := labelling_well_defined bp bd g₂ g₁ S₂ S₁ heq_X.symm
    rw [hS_eq] at heq_X ⊢
    have h_wd := conjugation_well_defined bp bd g₂ g₁ S₁ heq_X.symm
    rw [h_wd]
    exact (properParabolicRepr_eq bp Q).symm

  map_rel_iff' := by
    intro X Y
    show (conjugationForward bp X : Set G) ⊆ (conjugationForward bp Y : Set G) ↔
         (X : Set G) ⊆ (Y : Set G)
    simp only [conjugationForward]
    set g₁ := bp.specialSubsetReprG X
    set S₁ := bp.specialSubsetReprS X
    set g₂ := bp.specialSubsetReprG Y
    set S₂ := bp.specialSubsetReprS Y
    have heq₁ := specialSubsetRepr_eq bp X
    have heq₂ := specialSubsetRepr_eq bp Y
    constructor
    · intro h
      rw [heq₁, heq₂]
      exact conjugation_reflects_order bp bd ax g₁ g₂ S₁ S₂ h
    · intro h
      have h' : bp.leftCoset g₁ S₁ ⊆ bp.leftCoset g₂ S₂ := by rw [← heq₁, ← heq₂]; exact h
      exact conjugation_mono bp bd g₁ g₂ S₁ S₂ h'

end BNPair
