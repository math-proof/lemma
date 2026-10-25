/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexDecayTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexCriticalReduction.Part5
import Theorem.StatisticalMechanics.Code.FK.TriHexCoarseGeometry.Part3
import Def.StatisticalMechanics.Code.FK.TriHexDecayTransport
open Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W]


theorem subcriticalTwoPointExponentialDecay_of_comparison
    [Countable V] [Countable W]
    {P : PeriodicGraph V} {Q : PeriodicGraph W}
    {q pcP pcQ : Real}
    (hcompare : SubcriticalTwoPointComparison P Q q pcP pcQ)
    (hdecay : SubcriticalTwoPointExponentialDecay P q pcP) :
    SubcriticalTwoPointExponentialDecay Q q pcQ := by
  intro p hp
  obtain ⟨pP, hpP, K, a, b, hK, ha, hb, f, hprob, hdist⟩ :=
    hcompare p hp
  obtain ⟨c, C, hc, hC, hsource⟩ := hdecay pP hpP
  refine ⟨c * a, K * C * Real.exp (c * b), mul_pos hc ha,
    mul_pos (mul_pos hK hC) (Real.exp_pos _), ?_⟩
  intro x y
  have hexp :
      Real.exp (-c * (P.graph.dist (f x) (f y) : Real)) ≤
        Real.exp (c * b) *
          Real.exp (-(c * a) * (Q.graph.dist x y : Real)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hd := hdist x y
    nlinarith
  calc
    Q.wiredTwoPointProbability p q x y ≤
        K * P.wiredTwoPointProbability pP q (f x) (f y) := hprob x y
    _ ≤ K * (C * Real.exp
        (-c * (P.graph.dist (f x) (f y) : Real))) := by
      gcongr
      exact hsource (f x) (f y)
    _ ≤ K * (C * (Real.exp (c * b) *
        Real.exp (-(c * a) * (Q.graph.dist x y : Real)))) := by
      gcongr
    _ = (K * C * Real.exp (c * b)) *
        Real.exp (-(c * a) * (Q.graph.dist x y : Real)) := by ring


end PeriodicPlanar
end FK
end StatMech
