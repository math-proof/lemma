module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
public import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
public import Theorem.StatisticalMechanics.Code.Universality.DualEventSetEquality.Part4
public import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
public import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose.Part3
public import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
public import Theorem.StatisticalMechanics.Code.Universality.MatchedPlanarDualityClose.Part5
public import Theorem.StatisticalMechanics.Code.Universality.GreenEdgesClosureClose.Part6
open Set SimpleGraph Finset MeasureTheory
open StatMech.Lattice
open StatMech.RSW.Box


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenStubClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Universality

theorem gst_greenConfig_eq_negConfig_in_box (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {x y : Site 2} (hx : x ∈ rect 0 (n + 1) 0 n) (hy : y ∈ rect 0 (n + 1) 0 n) :
    gec2_greenConfig ω n s(x, y) = des_negConfig ω s(x, y) := by
  unfold gec2_greenConfig
  have hnot : s(x, y) ∉ gec2_greenSet n := by
    unfold gec2_greenSet
    simp only [Set.mem_setOf_eq, bdEdge_mk]
    intro h; exact (h.mp hx) hy
  simp [hnot]


end Universality
end StatMech
