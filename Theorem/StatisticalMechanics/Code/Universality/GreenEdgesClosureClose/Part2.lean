/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenEdgesClosureClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Universality.RSWBxpAssembly.Part2
import Def.StatisticalMechanics.Code.Universality.GreenEdgesClosureClose
open Set SimpleGraph Finset MeasureTheory
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem gec2_greenConfig_ge_negConfig (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    des_negConfig ω ≤ gec2_greenConfig ω n := by
  intro e
  unfold gec2_greenConfig
  cases h : des_negConfig ω e <;> simp_all


end Universality
end StatMech
