/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.AffineSLV.Part4
import Lemma.Set.IsHomothetic_πLattice
import Lemma.Set.ConjSet.eq.Image
import Structure.v1.Atlas.Buildings.code.Building.GroupApplicationsCh17
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Topology.Algebra.Group.Matrix
import Def.v1.Atlas.Buildings.code.Building.AffineSLVStrong.Part4
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace AffineBuildingSLVStrong

open AffineBuildingSLV AffineBuildingSLVAxioms


/-- Axiomatic action of $SL_V(k)$ on the Bruhat-Tits building of $SL_V$: a
simplicial action together with the induced action on apartments and frames, and
sufficient hypotheses to run strong-transitivity arguments (preservation of
maximal simplices, frame/apartment compatibility, building chain data and
within-apartment chamber transitivity). -/
structure SLVAction (C : DVRContext) where
  act_simplex : SLV C → Simplex C → Simplex C
  act_mul : ∀ (g₁ g₂ : SLV C) (σ : Simplex C),
    act_simplex (g₁ * g₂) σ = act_simplex g₁ (act_simplex g₂ σ)
  act_one : ∀ (σ : Simplex C), act_simplex 1 σ = σ
  act_apartment : SLV C → Set (Simplex C) → Set (Simplex C)
  act_apartment_eq : ∀ (g : SLV C) (A : Set (Simplex C)),
    act_apartment g A = (act_simplex g) '' A
  act_preserves_maximal : ∀ (g : SLV C) (σ : Simplex C),
    σ.IsMaximal C → (act_simplex g σ).IsMaximal C
  act_frame : SLV C → Frame C → Frame C
  act_apartment_frame_compat : ∀ (g : SLV C) (F : Frame C),
    act_apartment g (Apartment C F) = Apartment C (act_frame g F)
  act_apartment_surj : ∀ (max_apts : Set (Set (Simplex C))),
    (∀ F : Frame C, Apartment C F ∈ max_apts) →
    ∀ (A' A₀ : Set (Simplex C)), A' ∈ max_apts → A₀ ∈ max_apts →
    ∀ g : SLV C, (∀ x ∈ A', act_simplex g x ∈ A₀) →
    (fun x => act_simplex g x) '' A' = A₀
  act_building_chain_data :
    ∀ (max_apts : Set (Set (Simplex C))),
    (∀ F : Frame C, Apartment C F ∈ max_apts) →
    ∀ (B : Subgroup (SLV C)) (A₀ : Set (Simplex C)),
    A₀ ∈ max_apts →
    ∀ (C₀ : Set (Simplex C)),
    C₀ ⊆ A₀ →
    (B : Set (SLV C)) = pointwiseFixer act_simplex C₀ →
    ∀ (A' : Set (Simplex C)), A' ∈ max_apts →
      C₀ ⊆ A' ∧
      ∃ (enum : ℕ → Simplex C),
        (∀ σ ∈ A', ∃ n, enum n = σ) ∧
        (∀ n, enum n ∈ A') ∧
        ∀ (Y : Set (Simplex C)), C₀ ⊆ Y → Y ⊆ A' →
          ∃ (A_i : Set (Simplex C)) (b_i : SLV C),
            Y ⊆ A_i ∧ b_i ∈ B ∧
            (∀ x ∈ A_i, act_simplex b_i x ∈ A₀)
  act_frame_chamber_trans :
    ∀ (F : Frame C) (C₁ C₂ : Simplex C),
      C₁.IsMaximal C → C₂.IsMaximal C →
      C₁ ∈ Apartment C F → C₂ ∈ Apartment C F →
      ∃ g : SLV C, act_simplex g C₁ = C₂ ∧
        act_apartment g (Apartment C F) = Apartment C F


end AffineBuildingSLVStrong
