module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
public import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
public import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
public import Theorem.StatisticalMechanics.Code.Universality.DualCircuitToWalk.Part4
public import Theorem.StatisticalMechanics.Code.Universality.FaceDualDichotomy
public import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
public import Theorem.StatisticalMechanics.Code.Universality.G3PercDualityFull.Part2
public import Def.StatisticalMechanics.Code.Universality.FrameChangeIso
open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open StatMech.Lattice
open StatMech.RSW.Box


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FrameChangeIso.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}


theorem fci_faceWalk_to_dualWalk_support (S : Set (Site 2)) {u v : Site 2}
    (c : (faceBoundaryGraph S).Walk u v) :
    (fci_faceWalk_to_dualWalk S c).support = c.support := by
  rw [fci_faceWalk_to_dualWalk, SimpleGraph.Walk.support_mapLe_eq_support]


theorem fci_faceCycle_to_dualCycle (S : Set (Site 2)) {u : Site 2}
    (c : (faceBoundaryGraph S).Walk u u) (hc : c.IsCycle) :
    (fci_faceWalk_to_dualWalk S c).IsCycle :=
  hc.mapLe (fci_faceBoundaryGraph_le_dualLattice S)


end Universality
end StatMech
