/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineIsometryGroups/StrongTransitivity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Class.v1.Atlas.Buildings.code.Valuation.LatticesValuations
public import Theorem.Nat.IsInO
public import Theorem.Fin.SquareDetV'.eq.One.of.All_Eq.Nondegenerate
public import Def.v1.Atlas.Buildings.code.GeometricAlgebra.BilinearForms
public import Def.v1.Atlas.Buildings.code.Building.Affine.Part2
public import Def.v1.Atlas.Buildings.code.SphericalBuilding.IsometryGroups.Part3
public import Def.v1.Atlas.Buildings.code.SphericalBuilding.Oriflamme.Part5
public section

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false


namespace AffineIsometryBuilding

open DVRContext


variable (C : DVRContext)

/-- A primitive lattice $\Lambda$ over $\mathfrak{o}$ on which the
bilinear form $B$ is alternating: $B(v, v) = 0$ for every $v$. -/
structure PrimitiveLatticeAlternating extends DVRContext.PrimitiveLattice C where
  form_alternating : ∀ v : Fin C.n → C.k, form v v = 0

end AffineIsometryBuilding
