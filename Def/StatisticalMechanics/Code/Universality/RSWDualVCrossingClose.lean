module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
public import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
public import Theorem.StatisticalMechanics.Code.Universality.DualCutToPath.Part4
public import Theorem.StatisticalMechanics.Code.Universality.DualCircuitToWalk.Part4
public import Theorem.StatisticalMechanics.Code.Universality.PlanarDualCutConnected.Part5
public import Theorem.StatisticalMechanics.Code.Universality.FaceDualDichotomy
public import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
public import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose.Part3
public import Theorem.StatisticalMechanics.Code.Universality.RSWDualVCrossingClose
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWDualVCrossingClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Universality

def rdv_FrameReconcile (Φ : Site 2 → Site 2) : Prop :=
  ∀ (f g : Site 2), (hypercubicLattice 2).Adj f g →
    sharedPrimalEdge f g = s(rot90Inv (Φ f), rot90Inv (Φ g))


end Universality
end StatMech
