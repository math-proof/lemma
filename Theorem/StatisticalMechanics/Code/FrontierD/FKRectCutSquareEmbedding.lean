/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCrossingExploration.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part12
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConsumer.Part5
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQTranslation.Part2
import Theorem.StatisticalMechanics.Code.FK.TwoPointPositiveFull
open MeasureTheory StatMech.Lattice SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem freeBoxEvent_le_freeInfinite
    (N : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 (FK.boxVerts 2 N)))}
    (hA : IsIncreasing A) :
    (∑ omega,
        A.indicator (fun _ => (1 : Real)) omega *
          FK.fkProb (FK.boxGraph 2 N) p q omega) ≤
      (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (FK.boxRestrict 2 N ⁻¹' A) := by
  have hmeas : MeasurableSet (FK.boxRestrict 2 N ⁻¹' A) :=
    (FK.continuous_boxRestrict 2 N).measurable MeasurableSet.of_discrete
  rw [← FK.freeFiniteMeasure_real_boxRestrictEvent
    N hp hp1 (zero_lt_one.trans_le hq) A hmeas]
  apply ge_of_tendsto
    (FK.fkgq_free_infinite_measure N hp hp1 hq hA)
  filter_upwards [Filter.eventually_ge_atTop N] with m hm
  induction m, hm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hNm ih =>
      exact ih.trans (FK.fkgq_free_succ N m hNm hp hp1 hq hA)


end
end StatMech.FrontierD
