/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCriticalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalReduction.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.FKTrihexDuality
import Theorem.StatisticalMechanics.Code.FK.TriHexCriticalReduction
open MeasureTheory Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open BeffaraDC FrontierA

variable {V W : Type*} [DecidableEq V] [DecidableEq W]


noncomputable def PeriodicGraph.wiredTwoPointProbability
    [Countable V] (P : PeriodicGraph V) (p q : ℝ) (x y : V) : ℝ :=
  if h : p ∈ Ioo (0 : ℝ) 1 ∧ 0 < q then
    ((P.wiredBufferedInfiniteVolume h.1.1 h.1.2 h.2 :
        ProbabilityMeasure (ConfigSpace (Sym2 V))) :
      Measure (ConfigSpace (Sym2 V))).real (P.twoPointEvent x y)
  else 0

end PeriodicPlanar
end FK
end StatMech
