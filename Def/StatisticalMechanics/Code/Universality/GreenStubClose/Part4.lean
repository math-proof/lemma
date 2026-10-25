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
import Theorem.StatisticalMechanics.Code.Universality.GreenStubClose.Part4
open Set SimpleGraph Finset MeasureTheory
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

def gst_fullWireSet (n : ℤ) : Set (Sym2 (Site 2)) :=
  {e | ∃ x y : Site 2, e = s(x, y) ∧ x ∈ rect (-n) 0 0 (n + 1) ∧ y ∈ rect (-n) 0 0 (n + 1) ∧
    x 0 = -n ∧ y 0 = -n}


noncomputable def gst_fullWireConfig (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    ConfigSpace (Sym2 (Site 2)) := by
  classical
  exact fun e => if e ∈ gst_fullWireSet n then true else dualConfig ω e

end Universality
end StatMech
