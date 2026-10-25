/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.PressureDiff
import Theorem.StatisticalMechanics.Code.FK.DlrSandwich
import Theorem.StatisticalMechanics.Code.FK.Uniqueness
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Def.StatisticalMechanics.Code.FK.FKUniquenessFull.Part2
open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open ConfigSpace


section InfiniteVolume

open StatMech.Lattice


theorem wiredEdgeDensity_monotone_of_pressure (d : ℕ) (q : ℝ) (e : Sym2 (Site d))
    {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hb_eq : ∀ p, wiredEdgeDensity d q e p = pressureRightDeriv g p) :
    Monotone (wiredEdgeDensity d q e) := by
  have hfun : wiredEdgeDensity d q e = pressureRightDeriv g := funext hb_eq
  rw [hfun]
  exact pressureRightDeriv_monotone hg


theorem fk_uniqueness_off_countable (d : ℕ) (q : ℝ) (e : Sym2 (Site d))
    (hb : Monotone (wiredEdgeDensity d q e))
    (heq_at_cont : ∀ p, ContinuousAt (wiredEdgeDensity d q e) p →
      freeEdgeDensity d q e p = wiredEdgeDensity d q e p)
    (hcrit : ∀ p, freeEdgeDensity d q e p = wiredEdgeDensity d q e p →
      ∀ A : Set (ConfigSpace (Sym2 (Site d))), IsIncreasing A →
        ∀ {hp : 0 < p} {hp1 : p < 1} {hq : 0 < q},
          (freeInfiniteVolume d hp hp1 hq : Measure _).real A
            = (wiredInfiniteVolume d hp hp1 hq : Measure _).real A) :
    ∀ {hq : 0 < q}, ∃ S : Set ℝ, S.Countable ∧
      ∀ p ∉ S, ∀ (hp : 0 < p) (hp1 : p < 1) (phi : Measure (ConfigSpace (Sym2 (Site d)))),
        (∀ A : Set (ConfigSpace (Sym2 (Site d))), IsIncreasing A →
          (freeInfiniteVolume d hp hp1 hq : Measure _).real A ≤ phi.real A
            ∧ phi.real A ≤ (wiredInfiniteVolume d hp hp1 hq : Measure _).real A) →
        ∀ A : Set (ConfigSpace (Sym2 (Site d))), IsIncreasing A →
          phi.real A = (freeInfiniteVolume d hp hp1 hq : Measure _).real A
            ∧ phi.real A = (wiredInfiniteVolume d hp hp1 hq : Measure _).real A := by
  intro hq
  
  refine ⟨{p : ℝ | freeEdgeDensity d q e p ≠ wiredEdgeDensity d q e p},
    countable_density_ne hb heq_at_cont, ?_⟩
  intro p hp hp0 hp1 phi hsand A hA
  
  simp only [mem_setOf_eq, not_not] at hp
  
  have hfw : (freeInfiniteVolume d hp0 hp1 hq : Measure _).real A
      = (wiredInfiniteVolume d hp0 hp1 hq : Measure _).real A :=
    hcrit p hp A hA (hp := hp0) (hp1 := hp1) (hq := hq)
  
  exact dlr_sandwich_unique (hsand A hA) hfw

end InfiniteVolume
end FK
end StatMech
