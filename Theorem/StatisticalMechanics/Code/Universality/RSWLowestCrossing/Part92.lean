/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part90
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_pimsEdgeEquiv_apply (e : Sym2 (Site 2)) :
    rlc_pimsEdgeEquiv e =
      fci_faceEdgeEquiv (e.map rlc_dualReflect.symm) := by
  simp [rlc_pimsEdgeEquiv, Equiv.trans_apply,
    rlc_dualReflectEdge_symm_apply]


theorem rlc_dualReflectConfig_eq_pims
    (omega : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    rlc_dualReflectConfig omega e = !(omega (rlc_pimsEdgeEquiv e)) := by
  rw [rlc_dualReflectConfig_apply, rlc_pimsEdgeEquiv_apply,
    fci_faceDualConfig]


theorem rlc_pimsEdgeEquiv_reflected_mk_of_adj
    {f g : Site 2} (hfg : (hypercubicLattice 2).Adj f g) :
    rlc_pimsEdgeEquiv s(rlc_dualReflect f, rlc_dualReflect g) =
      sharedPrimalEdge f g := by
  rw [rlc_pimsEdgeEquiv_apply, Sym2.map_mk]
  simp only [Equiv.symm_apply_apply]
  exact fci_faceEdgeEquiv_mk_of_adj hfg


theorem rlc_pimsEdgeEquiv_horizontal (a b : ℤ) :
    rlc_pimsEdgeEquiv s(![a, b], ![a + 1, b]) =
      s(![-a - 1, b - 1], ![-a - 1, b]) := by
  rw [rlc_pimsEdgeEquiv_apply, Sym2.map_mk]
  have hadj : (hypercubicLattice 2).Adj
      (![-a - 1, b - 1] : Site 2) ![-a - 2, b - 1] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hx : rlc_dualReflect.symm (![(a : ℤ), b] : Site 2) =
      ![-a - 1, b - 1] := by
    ext i
    fin_cases i <;> simp
  have hy : rlc_dualReflect.symm (![a + 1, b] : Site 2) =
      ![-a - 2, b - 1] := by
    ext i
    fin_cases i <;> simp <;> ring
  have hleft : (![-a - 2, b - 1] : Site 2) =
      ![(-a - 1) - 1, b - 1] := by
    congr 1 <;> ring
  rw [hx, hy, fci_faceEdgeEquiv_mk_of_adj hadj, hleft,
    sharedPrimalEdge_left]
  simp [faceCorner00, faceCorner01]


theorem rlc_pimsEdgeEquiv_vertical (a b : ℤ) :
    rlc_pimsEdgeEquiv s(![a, b], ![a, b + 1]) =
      s(![-a - 1, b], ![-a, b]) := by
  rw [rlc_pimsEdgeEquiv_apply, Sym2.map_mk]
  have hadj : (hypercubicLattice 2).Adj
      (![-a - 1, b - 1] : Site 2) ![-a - 1, b] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hx : rlc_dualReflect.symm (![(a : ℤ), b] : Site 2) =
      ![-a - 1, b - 1] := by
    ext i
    fin_cases i <;> simp
  have hy : rlc_dualReflect.symm (![a, b + 1] : Site 2) =
      ![-a - 1, b] := by
    ext i
    fin_cases i <;> simp
  have htop : (![-a - 1, b] : Site 2) =
      ![-a - 1, (b - 1) + 1] := by
    congr 1 <;> ring
  rw [hx, hy, fci_faceEdgeEquiv_mk_of_adj hadj, htop,
    sharedPrimalEdge_top]
  simp [faceCorner01, faceCorner11]


theorem rlc_reflectedEdge_eq_horizontal_of_shared_vertical
    {f g : Site 2} (hfg : (hypercubicLattice 2).Adj f g) {t : ℤ}
    (hshared : sharedPrimalEdge f g = s(![0, t], ![0, t + 1])) :
    s(rlc_dualReflect f, rlc_dualReflect g) =
      s(![-1, t + 1], ![0, t + 1]) := by
  apply rlc_pimsEdgeEquiv.injective
  rw [rlc_pimsEdgeEquiv_reflected_mk_of_adj hfg, hshared]
  symm
  simpa using (rlc_pimsEdgeEquiv_horizontal (-1) (t + 1))


theorem rlc_dualReflectConfig_mk
    (omega : ConfigSpace (Sym2 (Site 2))) (x y : Site 2) :
    rlc_dualReflectConfig omega
        s(rlc_dualReflect x, rlc_dualReflect y) =
      fci_faceDualConfig omega s(x, y) := by
  rw [rlc_dualReflectConfig_apply, Sym2.map_mk]
  simp


theorem rlc_dualReflectConfig_measurePreserving :
    MeasurePreserving rlc_dualReflectConfig
      rba_selfDualMeasure rba_selfDualMeasure := by
  have hreindex : MeasurePreserving
      (Equiv.piCongrLeft (fun _ => Bool) rlc_dualReflectEdge)
      rba_selfDualMeasure rba_selfDualMeasure := by
    refine ⟨(MeasurableEquiv.piCongrLeft
      (fun _ => Bool) rlc_dualReflectEdge).measurable, ?_⟩
    rw [rba_selfDualMeasure]
    unfold bernoulliProductMeasure
    exact Measure.infinitePi_map_piCongrLeft
      (fun _ : Sym2 (Site 2) =>
        bernoulliMeasure (2⁻¹ : ℝ≥0) half_le_one)
      rlc_dualReflectEdge
  exact hreindex.comp fci_faceDualConfig_measurePreserving


end Universality
end StatMech
