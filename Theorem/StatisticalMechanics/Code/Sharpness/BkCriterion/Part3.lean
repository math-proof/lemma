/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Def.StatisticalMechanics.Code.Sharpness.BkCriterion.Part2
open MeasureTheory Finset
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace


variable {E : Type*}


variable {V : Type*}


lemma ConnWithin.mono_config (G : SimpleGraph V) {ω ω' : ConfigSpace (Sym2 V)} (h : ω ≤ ω')
    {A : Set V} {x y : A} (hc : ConnWithin G ω A x y) : ConnWithin G ω' A x y :=
  hc.mono (fun _ _ hab => openSub_mono G h hab)


end Sharpness
end StatMech
