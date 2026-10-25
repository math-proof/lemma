/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Graph.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierClose.Part2
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Def.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Walls


theorem kwg_dualContourMatching_of_cutMatching (P : PlanarZ2Subgraph)
    (β βstar : ℝ) (htemp : Real.tanh βstar = Real.exp (-2 * β))
    (hmatch : kwg_GeometricCutEvenMatching P (Real.exp (-2 * β)) 2) :
    kwg_DualContourMatching P β βstar
      ((2 : ℝ) ^ Nat.card (kwg_Face P) *
        (Real.cosh βstar) ^ Nat.card (kwg_Edge P) /
        (Real.exp (β * P.G.edgeSet.ncard) * 2)) := by
  classical
  letI : Fintype P.V := Fintype.ofFinite P.V
  letI : Fintype (kwg_Face P) := Fintype.ofFinite (kwg_Face P)
  refine ⟨htemp, ?_⟩
  unfold kwg_GeometricCutEvenMatching kwg_CutEvenMatching at hmatch
  rw [kwg_primalCut_sum P] at hmatch
  rw [isingZ_low_temp_expansion P.G β]
  have hedgecard : P.G.edgeFinset.card = P.G.edgeSet.ncard := by
    rw [Set.ncard_eq_toFinset_card P.G.edgeSet]
    congr 1
    ext e
    simp
  rw [hedgecard]
  rw [← htemp] at hmatch ⊢
  set Sd := ∑ F : Finset (kwg_Edge P),
    if kwg_IsEven (kwg_dualEnds P) F then (Real.tanh βstar) ^ F.card else 0
  have hexp : (0 : ℝ) < Real.exp (β * P.G.edgeFinset.card) := Real.exp_pos _
  change _ * _ * Sd = _
  change _ = 2 * Sd at hmatch
  rw [hmatch]
  field_simp


theorem kwg_isingZ_duality_of_cutMatching (P : PlanarZ2Subgraph)
    (β βstar : ℝ) (htemp : Real.tanh βstar = Real.exp (-2 * β))
    (hmatch : kwg_GeometricCutEvenMatching P (Real.exp (-2 * β)) 2) : by
    letI : Fintype P.V := Fintype.ofFinite P.V
    letI : Fintype (kwg_Face P) := Fintype.ofFinite (kwg_Face P)
    letI : DecidableEq (kwg_Face P) := Classical.decEq _
    exact kwg_isingZ (kwg_dualEnds P) βstar =
      ((2 : ℝ) ^ Nat.card (kwg_Face P) *
        (Real.cosh βstar) ^ Nat.card (kwg_Edge P) /
        (Real.exp (β * P.G.edgeSet.ncard) * 2)) * isingZ P.G β 0 := by
  classical
  letI : Fintype P.V := Fintype.ofFinite P.V
  letI : Fintype (kwg_Face P) := Fintype.ofFinite (kwg_Face P)
  have hdcm := kwg_dualContourMatching_of_cutMatching P β βstar htemp hmatch
  obtain ⟨_, hdcm⟩ := hdcm
  rw [kwg_isingZ_high_temp]
  simpa only [Nat.card_eq_fintype_card] using hdcm


theorem kwg_isingZ_duality (P : PlanarZ2Subgraph)
    (β βstar : ℝ) (htemp : Real.tanh βstar = Real.exp (-2 * β)) :
    kwg_isingZ (kwg_dualEnds P) βstar =
      ((2 : ℝ) ^ Nat.card (kwg_Face P) *
        (Real.cosh βstar) ^ Nat.card (kwg_Edge P) /
        (Real.exp (β * P.G.edgeSet.ncard) *
          (2 : ℝ) ^ Nat.card P.G.ConnectedComponent)) * isingZ P.G β 0 := by
  classical
  have hmatch := kwg_geometricCutEvenMatching P (Real.exp (-2 * β))
  unfold kwg_GeometricCutEvenMatching kwg_CutEvenMatching at hmatch
  rw [kwg_primalCut_sum P] at hmatch
  rw [kwg_isingZ_high_temp, isingZ_low_temp_expansion P.G β]
  have hedgecard : P.G.edgeFinset.card = P.G.edgeSet.ncard := by
    rw [Set.ncard_eq_toFinset_card P.G.edgeSet]
    congr 1
    ext e
    simp
  rw [hedgecard]
  rw [← htemp] at hmatch ⊢
  set Sd := ∑ F : Finset (kwg_Edge P),
    if kwg_IsEven (kwg_dualEnds P) F then (Real.tanh βstar) ^ F.card else 0
  set mult : ℝ := (2 : ℝ) ^ Nat.card P.G.ConnectedComponent
  change _ * _ * Sd = _
  change _ = mult * Sd at hmatch
  rw [hmatch]
  have hexp : Real.exp (β * (P.G.edgeSet.ncard : ℝ)) ≠ 0 := (Real.exp_pos _).ne'
  have hmult : mult ≠ 0 := by
    exact pow_ne_zero _ (by norm_num)
  field_simp
  simp only [Nat.card_eq_fintype_card]
  ring

end Ising
end StatMech
