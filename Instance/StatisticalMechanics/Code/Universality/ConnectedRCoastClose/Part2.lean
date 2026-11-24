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
public import Def.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part7
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

noncomputable instance crr_LRFaceGraph_locallyFinite
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) :
    SimpleGraph.LocallyFinite (crr_LRFaceGraph omega n) := fun f => by
  let toLat : (crr_LRFaceGraph omega n).neighborSet f →
      (hypercubicLattice 2).neighborSet f := fun z => ⟨z.1, z.2.1.1⟩
  exact Fintype.ofInjective toLat (fun _ _ h => Subtype.ext
    (congrArg (fun z : (hypercubicLattice 2).neighborSet f => (z : Site 2)) h))


end Universality
end StatMech
