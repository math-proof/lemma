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
public import Theorem.StatisticalMechanics.Code.Universality.RSWBxpAssembly.Part2
public import Def.StatisticalMechanics.Code.Universality.GreenEdgesClosureClose.Part4
open Set SimpleGraph Finset MeasureTheory
open StatMech.Lattice
open StatMech.RSW.Box


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenEdgesClosureClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Universality

theorem gec2_dichotomy_of_greenJordan (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (_hnoH : ¬ HorizontalCrossing ω 0 (n + 1) 0 n) (h : gec2_GreenJordan ω n) :
    HorizontalCrossing ω 0 (n + 1) 0 n ∨ gec2_GreenMatchedFrame ω n :=
  Or.inr h


theorem gec2_greenJordan_of_matchedFrameDualV (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (h : mpd_MatchedFrameDualV ω n) : gec2_GreenJordan ω n :=
  gec2_greenMatchedFrame_of_matchedFrameDualV ω n h


end Universality
end StatMech
