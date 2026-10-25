/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonPairLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonInterpolation.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.MassTransport
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonPairLaw.Part2
open MeasureTheory


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


@[simp] theorem pairSiteLeft_interpolatedHighPair
    (T : MonotoneAutomaton d) (q : FieldTriple d) :
    pairSiteLeft (interpolatedHighPair T q) = interpolatedSite T q := rfl

@[simp] theorem pairSiteRight_interpolatedHighPair
    (T : MonotoneAutomaton d) (q : FieldTriple d) :
    pairSiteRight (interpolatedHighPair T q) = T q.2.2 := rfl


theorem measurable_interpolatedHighPair (T : MonotoneAutomaton d) :
    Measurable (interpolatedHighPair T : FieldTriple d → PairSiteConfig d) := by
  unfold interpolatedHighPair
  exact measurable_pairSiteConfig.comp
    ((measurable_interpolatedSite T).prodMk
      (T.measurable_toFun.comp measurable_snd.snd))


theorem interpolatedHighPair_shift (T : MonotoneAutomaton d)
    (g : Multiplicative (Site d)) (q : FieldTriple d) :
    interpolatedHighPair T (tripleFieldShift g q) =
      shift g (interpolatedHighPair T q) := by
  unfold interpolatedHighPair
  rw [interpolatedSite_shift, tripleFieldShift_snd_snd,
    T.equivariant, pairSiteConfig_shift]


end StatMech.FrontierA
