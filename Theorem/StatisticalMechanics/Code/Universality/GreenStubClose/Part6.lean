/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenStubClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Universality.DualEventSetEquality.Part4
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.MatchedPlanarDualityClose.Part5
import Theorem.StatisticalMechanics.Code.Universality.GreenEdgesClosureClose.Part6
import Def.StatisticalMechanics.Code.Universality.GreenStubClose.Part5
open Set SimpleGraph Finset MeasureTheory
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem gst_dichotomy_of_genuine (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) (h : gst_genuine_residue ω n) :
    HorizontalCrossing ω 0 n 0 n ∨ DualVerticalCrossing ω 0 n 0 n :=
  jex_exhaustivity_of_barrier ω n hnoH h


theorem gst_genuine_residue_nonvacuous : gst_genuine_residue bcc_botCfg 2 :=
  jex_barrier_vcrossing_nonvacuous


theorem gst_matched_half_of_greenDichotomy (n : ℤ)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 (n + 1) 0 n))
    (hmeasV : MeasurableSet (verticalCrossingEvent (-n) 0 0 (n + 1)))
    (hgreen : gec2_GreenDichotomy n)
    (hsym : rba_selfDualMeasure.real (verticalCrossingEvent (-n) 0 0 (n + 1))
              = rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n)) :
    (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n) :=
  gec2_matched_half_of_greenDichotomy n hmeasH hmeasV hgreen hsym


theorem gst_greenDichotomy_false (n : ℤ) (hn : 1 ≤ n) : ¬ gec2_GreenDichotomy n :=
  gec2_greenDichotomy_false n hn

end Universality
end StatMech
