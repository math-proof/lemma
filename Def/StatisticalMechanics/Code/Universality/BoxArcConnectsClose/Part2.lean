module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
public import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
public import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
public import Theorem.StatisticalMechanics.Code.Universality.FaceDualDichotomy
public import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
public import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
public import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose.Part3
public import Theorem.StatisticalMechanics.Code.Universality.RSWDualVCrossingClose.Part2
public import Theorem.StatisticalMechanics.Code.Universality.PlanarMengerDualityClose.Part4
public import Theorem.StatisticalMechanics.Code.Universality.MengerBarrierClose.Part2
public import Theorem.StatisticalMechanics.Code.Universality.CoastlineContinuityClose.Part2
public import Theorem.StatisticalMechanics.Code.Universality.CoastlineAnchorClose.Part3
public import Theorem.StatisticalMechanics.Code.Universality.CircuitReachClose.Part2
public import Theorem.StatisticalMechanics.Code.Universality.BoxArcConnectsClose
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxArcConnectsClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Universality

def bac_IsRCoastFace (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (f : Site 2) : Prop :=
  (∃ g : Site 2, (pmd_boxFaceBarrier ω n).Adj f g) ∧
    (∃ p : Site 2, p ∈ bac_rightComplement ω n ∧
      (p = ![f 0, f 1] ∨ p = ![f 0 + 1, f 1] ∨ p = ![f 0, f 1 + 1] ∨ p = ![f 0 + 1, f 1 + 1]))


end Universality
end StatMech
