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
public import Def.StatisticalMechanics.Code.Universality.GreenStubClose.Part2
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

theorem gst_greenDualConfig_open_iff (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (e : Sym2 (Site 2)) :
    gst_greenDualConfig ω n e = true ↔ e ∈ gst_greenSet n ∨ dualConfig ω e = true := by
  classical
  unfold gst_greenDualConfig
  by_cases h : e ∈ gst_greenSet n <;> simp [h]


theorem gst_greenDualConfig_ge (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    dualConfig ω ≤ gst_greenDualConfig ω n := by
  intro e
  cases h : dualConfig ω e
  · simp
  · rw [(gst_greenDualConfig_open_iff ω n e).mpr (Or.inr h)]


end Universality
end StatMech
