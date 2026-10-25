/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section35.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section34
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section34.Part3
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Colimit.Module
import Mathlib.Order.Cofinal
import Mathlib.Algebra.Exact
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
open Set


namespace CechCohomology

/-- A map `φ : J → I` between preorders is **cofinal** if every `i : I` is
$\le$ some `φ j`. Used to recognise when pulling a directed system back along
`φ` gives the same direct limit. -/
def IsCofinalMap {I : Type*} {J : Type*} [LE I] (φ : J → I) : Prop :=
  ∀ i : I, ∃ j : J, i ≤ φ j

section DirectLimits

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [DecidableEq ι] [Nonempty ι]

variable {κ : Type*} [Preorder κ] [IsDirectedOrder κ] [DecidableEq κ] [Nonempty κ]

variable (G : ι → Type*) [∀ i, AddCommGroup (G i)]

variable (f : ∀ i j, i ≤ j → G i →+ G j) [DirectedSystem G fun i j h ↦ f i j h]

variable (φ : κ →o ι)

/-- Pullback of the bonding maps of a directed system `(G, f)` along a monotone
map `φ : κ →o ι`: the pulled-back system has fibres `G (φ j)` and bonding maps
`f (φ j₁) (φ j₂) (φ.monotone h)`. -/
def pullbackBondingMap (j₁ j₂ : κ) (h : j₁ ≤ j₂) : G (φ j₁) →+ G (φ j₂) :=
  f (φ j₁) (φ j₂) (φ.monotone h)

/-- The canonical map from the direct limit of the pulled-back system over `κ`
to the direct limit over `ι` of the original system, induced by the universal
property of direct limits. -/
noncomputable def cofinalMap :
    AddCommGroup.DirectLimit (fun j => G (φ j)) (pullbackBondingMap G f φ) →+
    AddCommGroup.DirectLimit G f :=
  AddCommGroup.DirectLimit.lift _ _ _
    (fun j => AddCommGroup.DirectLimit.of G f (φ j))
    (fun _ _ hij x => AddCommGroup.DirectLimit.of_f (f := f) (φ.monotone hij) x)

/-- **Lemma 35.7 (cofinal maps and direct limits).** If `φ : κ →o ι` is cofinal
(every `i : ι` is `≤ φ j` for some `j : κ`), then the induced map between
direct limits is an additive equivalence: the limit over a cofinal subset
recovers the full limit. -/
noncomputable def cofinalMapEquiv
    (hcof : ∀ i : ι, ∃ j : κ, i ≤ φ j) :
    AddCommGroup.DirectLimit (fun j => G (φ j)) (pullbackBondingMap G f φ) ≃+
    AddCommGroup.DirectLimit G f :=
  AddEquiv.ofBijective (cofinalMap G f φ)
    ⟨by


      rw [← AddMonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro a ha
      rw [AddMonoidHom.mem_ker] at ha
      induction a using AddCommGroup.DirectLimit.induction_on with
      | ih j x =>
        simp only [cofinalMap, AddCommGroup.DirectLimit.lift_of] at ha
        obtain ⟨i, hji, hzero⟩ := AddCommGroup.DirectLimit.of.zero_exact (φ j) x ha
        obtain ⟨j', hij'⟩ := hcof i
        obtain ⟨k, hjk, hj'k⟩ := directed_of (· ≤ ·) j j'
        have h_i_phik : i ≤ φ k := le_trans hij' (φ.monotone hj'k)
        have key : pullbackBondingMap G f φ j k hjk x = 0 := by
          show f (φ j) (φ k) (φ.monotone hjk) x = 0
          rw [show f (φ j) (φ k) (φ.monotone hjk) x =
                f i (φ k) h_i_phik (f (φ j) i hji x) from
            (DirectedSystem.map_map (f := fun i j h ↦ f i j h) hji h_i_phik x).symm]
          rw [hzero, map_zero]
        simp only [AddSubgroup.mem_bot]
        rw [show AddCommGroup.DirectLimit.of _ (pullbackBondingMap G f φ) j x =
          AddCommGroup.DirectLimit.of _ (pullbackBondingMap G f φ) k
            (pullbackBondingMap G f φ j k hjk x)
          from (AddCommGroup.DirectLimit.of_f (f := pullbackBondingMap G f φ) hjk x).symm]
        rw [key, map_zero],
    by
      intro a
      induction a using AddCommGroup.DirectLimit.induction_on with
      | ih i x =>
        obtain ⟨j, hij⟩ := hcof i
        exact ⟨AddCommGroup.DirectLimit.of _ (pullbackBondingMap G f φ) j
          (f i (φ j) hij x), by
          simp only [cofinalMap, AddCommGroup.DirectLimit.lift_of]
          exact AddCommGroup.DirectLimit.of_f (f := f) hij x⟩⟩

end DirectLimits
end CechCohomology
