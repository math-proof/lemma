module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.RSW.BoxCrossing.Part3
public import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
public import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
public import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
public import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
public import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
public import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
public import Theorem.StatisticalMechanics.Code.Universality.BXPAllAspect
public import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
public import Theorem.StatisticalMechanics.Code.Universality.PlanarMengerDualityClose.Part4
public import Theorem.StatisticalMechanics.Code.Universality.MengerBarrierClose.Part2
public import Theorem.StatisticalMechanics.Code.Universality.CoastlineContinuityClose.Part2
public import Theorem.StatisticalMechanics.Code.Universality.CoastlineAnchorClose.Part3
public import Theorem.StatisticalMechanics.Code.Universality.CircuitReachClose.Part2
public import Theorem.StatisticalMechanics.Code.Universality.BoxArcConnectsClose.Part4
public import Theorem.StatisticalMechanics.Code.Universality.RCoastMengerClose.Part2
public import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part12
open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped NNReal
open StatMech.Lattice
open StatMech.RSW.Box


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Universality

def crr_FaceConnectionEvent (n : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {eta | ∃ (a₀ a₁ : ℤ), 0 ≤ a₀ ∧ a₀ ≤ n - 1 ∧ 0 ≤ a₁ ∧ a₁ ≤ n - 1 ∧
    (openSubgraph 2 eta).Reachable ![a₀, -1] ![a₁, n]}


def crr_FaceDualConnectionEvent (n : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | pmd_FaceDualVCrossing ω n}


end Universality
end StatMech
