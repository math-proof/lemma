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
public import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose.Part2
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Universality

def bcc_dualBottomReach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Set (Site 2) :=
  {v | v ∈ rect 0 n 0 n ∧ ∃ (x : Site 2) (_hx : x ∈ bottomSide 0 n 0 n) (hv : v ∈ rect 0 n 0 n),
      ConnectedWithin 2 (dualConfig ω) (rect 0 n 0 n) ⟨x, bottomSide_subset _hx⟩ ⟨v, hv⟩}


end Universality
end StatMech
