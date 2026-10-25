/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/AeTailInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.CondDistribution.Part4
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Def.StatisticalMechanics.Code.Foundations.AeTailInvariant
open MeasureTheory MeasurableSpace Set Filter
open scoped ENNReal symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false


namespace StatMech

open ConfigSpace

variable {E H : Type*} [Countable E] [DecidableEq E]
  [Group H] [MulAction H E]


theorem atiFinSig_mono {F K : Finset E} (h : F ⊆ K) :
    atiFinSig F ≤ atiFinSig K :=
  iSup₂_mono' fun e he => ⟨e, h he, le_rfl⟩

theorem atiCylinderRing_isSetRing : IsSetRing (atiCylinderRing E) := by
  refine ⟨⟨∅, @MeasurableSet.empty _ (atiFinSig ∅)⟩, ?_, ?_⟩
  · rintro A B ⟨F, hA⟩ ⟨K, hB⟩
    exact ⟨F ∪ K,
      (atiFinSig_mono Finset.subset_union_left _ hA).union
        (atiFinSig_mono Finset.subset_union_right _ hB)⟩
  · rintro A B ⟨F, hA⟩ ⟨K, hB⟩
    exact ⟨F ∪ K,
      (atiFinSig_mono Finset.subset_union_left _ hA).diff
        (atiFinSig_mono Finset.subset_union_right _ hB)⟩

theorem atiCylinderRing_univ_mem :
    (Set.univ : Set (ConfigSpace E)) ∈ atiCylinderRing E :=
  ⟨∅, @MeasurableSet.univ _ (atiFinSig ∅)⟩

theorem atiCylinderRing_generateFrom :
    (inferInstance : MeasurableSpace (ConfigSpace E)) =
      generateFrom (atiCylinderRing E) := by
  apply le_antisymm
  · rw [measurableSpace_eq_iSup_comap]
    refine iSup_le fun e => fun A hA =>
      measurableSet_generateFrom ⟨{e}, ?_⟩
    have hsingle : atiFinSig ({e} : Finset E) =
        MeasurableSpace.comap (ConfigSpace.eval e) inferInstance := by
      simp [atiFinSig]
    rw [hsingle]
    exact hA
  · refine generateFrom_le ?_
    rintro A ⟨F, hF⟩
    exact (iSup₂_le fun e _ => (ConfigSpace.measurable_eval e).comap_le) A hF


end StatMech
