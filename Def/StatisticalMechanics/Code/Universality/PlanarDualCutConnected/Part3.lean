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
public import Theorem.StatisticalMechanics.Code.Universality.DualCutToPath.Part4
public import Theorem.StatisticalMechanics.Code.Universality.PlanarDualCutConnected.Part2
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}


def pdc_rot90InvHom (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    dcw_dualBarrierGraph ω n →g pdc_barrierGraphPrimal ω n where
  toFun := rot90Inv
  map_rel' := fun {p q} h => pdc_rot90Inv_adj_primal ω n h

end Universality
end StatMech
