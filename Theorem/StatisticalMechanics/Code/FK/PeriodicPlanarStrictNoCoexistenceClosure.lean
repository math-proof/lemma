/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictNoCoexistenceClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarStrictNoCoexistenceCapstone
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldExclusion
import Theorem.StatisticalMechanics.Code.FK.SecantClose.Part3
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarStrictNoCoexistenceClosure
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC

variable {V W : Type} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem PeriodicGraph.freeWiredIncreasingCylinderAgreementOffCountable_of_logistic
    (P : PeriodicGraph V) {q : Real}
    (hagrees : P.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic q) :
    P.FreeWiredIncreasingCylinderAgreementOffCountable q := by
  intro n
  apply ((hagrees n).image fsc_logistic).mono
  intro p hp
  have hphysical : p ∈ Ioo (0 : Real) 1 ∧ 0 < q := by
    by_contra hnot
    obtain ⟨S, hS, hne⟩ := hp
    apply hne
    simp only [PeriodicGraph.freeBufferedCylinderProbability,
      PeriodicGraph.wiredBufferedCylinderProbability, dif_neg hnot]
  refine ⟨fsc_logit p, ?_, fsc_logistic_logit hphysical.1.1 hphysical.1.2⟩
  obtain ⟨S, hS, hne⟩ := hp
  refine ⟨S, hS, ?_⟩
  simpa only [fsc_logistic_logit hphysical.1.1 hphysical.1.2] using hne


end StatMech.FK.PeriodicPlanar
