module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
public import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
public import Theorem.StatisticalMechanics.Code.Universality.FaceDualDichotomy
public import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
public import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
public import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose.Part3
public import Theorem.StatisticalMechanics.Code.Universality.RSWDualVCrossingClose.Part2
public import Theorem.StatisticalMechanics.Code.Universality.PlanarMengerDualityClose.Part4
public import Theorem.StatisticalMechanics.Code.Universality.MengerBarrierClose
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MengerBarrierClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Universality

def mbc_FrontierRungsConnect (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  ∀ (r : ℤ), 0 ≤ r → r ≤ n - 1 → ∀ (c c' : ℤ),
    mbc_IsRightFrontier ω n c r → mbc_IsRightFrontier ω n c' (r + 1) →
      (pmd_boxFaceBarrier ω n).Reachable ![c, r] ![c', r]


end Universality
end StatMech
