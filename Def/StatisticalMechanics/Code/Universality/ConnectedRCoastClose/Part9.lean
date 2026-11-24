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
public import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part8
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

noncomputable def crr_boxRCut
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) :
    Finset (Ising.kwg_Edge (crr_boxPlanar n)) :=
  Ising.kwg_cutSet (Ising.kwg_primalEnds (crr_boxPlanar n)) (crr_boxRColour omega n)


noncomputable def crr_boxFaceRep (n : Int) (C : Ising.kwg_Face (crr_boxPlanar n)) : Site 2 :=
  C.nonempty_supp.some

end Universality
end StatMech
