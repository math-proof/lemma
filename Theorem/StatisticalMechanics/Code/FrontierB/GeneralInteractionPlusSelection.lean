/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionPlusSelection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.GeneralInteractionPlusParity
open Filter MeasureTheory Set Topology
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Ising Lattice


theorem generalPlusCurrentLimit_pattern_factor_nonDiagonal
    {d : Nat} (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d))) (hSdiag : ∀ e ∈ S, ¬e.IsDiag)
    {nu : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi : Nat → Nat} (hphi : StrictMono phi)
    (hnu : WeakCurrentConverges
      ((fun n ↦ generalPlusBoxCurrentMeasure J hJ n beta hbeta.le) ∘ phi) nu)
    (a : ↑S → Nat) :
    (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentCylinder S {a}) =
      (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentParityPatternCylinder S (currentLocalParity a)) *
        nonnegativeFiniteParityPMF S (fun e ↦ beta * J e)
          (fun e : ↑S ↦ mul_nonneg hbeta.le (hJ e.1))
          (currentLocalParity a) a := by
  apply hnu.pattern_factor_of_eventually S
    (fun odd ↦ nonnegativeFiniteParityPMF S (fun e ↦ beta * J e)
      (fun e : ↑S ↦ mul_nonneg hbeta.le (hJ e.1)) odd)
    (fun odd b ↦ PMF.apply_ne_top
      (nonnegativeFiniteParityPMF S (fun e ↦ beta * J e)
        (fun e : ↑S ↦ mul_nonneg hbeta.le (hJ e.1)) odd) b)
  obtain ⟨N, hSN⟩ := finiteInteractionEdges_subset_box S
  intro b
  filter_upwards [eventually_ge_atTop N] with k hk
  apply generalPlusBoxCurrentMeasure_pattern_factor_nonDiagonal
    J hJ beta hbeta S
  · intro e he x hx
    exact box_mono d (show N ≤ 2 * phi k + 1 by
      exact hk.trans (hphi.id_le k) |>.trans (by omega)) (hSN e he x hx)
  · exact hSdiag


end StatMech.FrontierB
