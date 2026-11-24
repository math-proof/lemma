module
public import Mathlib
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
public import Theorem.StatisticalMechanics.Code.RSW.Defs.Part4
open Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace RSW

namespace Box

open StatMech.Lattice

open StatMech.TwoDim


def annulus (z : Site 2) (n : ℕ) : Set (Site 2) :=
  (fun x => z + x) '' (box 2 (2 * n) \ box 2 n)

end Box
end RSW
end StatMech
