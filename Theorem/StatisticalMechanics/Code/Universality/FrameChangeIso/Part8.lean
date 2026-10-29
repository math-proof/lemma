/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FrameChangeIso.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Theorem.StatisticalMechanics.Code.Universality.DualCircuitToWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.FaceDualDichotomy
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
import Theorem.StatisticalMechanics.Code.Universality.G3PercDualityFull.Part2
import Def.StatisticalMechanics.Code.Universality.FrameChangeIso.Part7
open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}


theorem fci_faceOpenDual_eq_openSubgraph (w : ConfigSpace (Sym2 (Site 2))) :
    fci_faceOpenDual w = openSubgraph 2 (fci_faceDualConfig w) := by
  ext f g
  constructor
  · rintro ⟨h, hclosed⟩
    refine ⟨h, ?_⟩
    rw [fci_faceDualConfig, fci_faceEdgeEquiv_mk_of_adj h]
    simpa using hclosed
  · rintro ⟨h, hopen⟩
    refine ⟨h, ?_⟩
    rw [fci_faceDualConfig, fci_faceEdgeEquiv_mk_of_adj h] at hopen
    simpa using hopen


theorem fci_faceDualConfig_measurePreserving :
    MeasurePreserving
      (fci_faceDualConfig : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2)))
      (bernoulliProductMeasure (2⁻¹ : NNReal) half_le_one)
      (bernoulliProductMeasure (2⁻¹ : NNReal) half_le_one) := by
  let reindex := Equiv.piCongrLeft (fun _ => Bool) fci_faceEdgeEquiv.symm
  have hreindex : MeasurePreserving reindex
      (bernoulliProductMeasure (2⁻¹ : NNReal) half_le_one)
      (bernoulliProductMeasure (2⁻¹ : NNReal) half_le_one) := by
    refine ⟨(MeasurableEquiv.piCongrLeft (fun _ => Bool) fci_faceEdgeEquiv.symm).measurable, ?_⟩
    unfold bernoulliProductMeasure
    exact Measure.infinitePi_map_piCongrLeft
      (fun _ : Sym2 (Site 2) => bernoulliMeasure (2⁻¹ : NNReal) half_le_one)
      fci_faceEdgeEquiv.symm
  have hcompl : MeasurePreserving
      (fun (eta : ConfigSpace (Sym2 (Site 2))) e => !(eta e))
      (bernoulliProductMeasure (2⁻¹ : NNReal) half_le_one)
      (bernoulliProductMeasure (2⁻¹ : NNReal) half_le_one) := by
    refine ⟨measurable_complement, ?_⟩
    rw [map_complement (2⁻¹ : NNReal) half_le_one]
    congr 1
    exact one_sub_half_eq
  have hcomp := hcompl.comp hreindex
  convert hcomp using 1 <;> funext w e <;>
    simp [fci_faceDualConfig, reindex, Equiv.piCongrLeft_apply]


theorem fci_square_dichotomy (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    (bcd_leftReach ω n).Finite ∧
      (∀ {v w : Site 2}, v ∈ bcd_leftReach ω n → w ∈ rect 0 n 0 n →
        (hypercubicLattice 2).Adj v w → w ∉ bcd_leftReach ω n →
        (openSubgraph 2 (dualConfig ω)).Adj (rot90Fun v) (rot90Fun w)) ∧
      (∃ f g : Site 2, (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g) ∧
      (∃ (u : Site 2) (c : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u),
        c.IsCycle ∧ (fci_faceWalk_to_dualWalk (bcd_leftReach ω n) c).IsCycle) := by
  obtain ⟨hfin, hbar, hne, ⟨u, c, hcyc⟩⟩ := fdd_square_dichotomy ω n hn hnoH
  exact ⟨hfin, hbar, hne, u, c, hcyc, fci_faceCycle_to_dualCycle _ c hcyc⟩

end Universality
end StatMech
