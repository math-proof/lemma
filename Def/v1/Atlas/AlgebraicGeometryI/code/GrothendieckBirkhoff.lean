module
public import Mathlib.Algebra.Module.PID
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.SheafCohomology.Part2
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.SheafCohomology
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.Lec10SheavesP1
public import Def.v1.Atlas.AlgebraicGeometryI.code.Lec10SheavesP1.Part3
public import Instance.v1.Atlas.AlgebraicGeometryI.code.GrothendieckBirkhoff


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckBirkhoff.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace GrothendieckBirkhoff

/-- Euler characteristic of `O(n)` on `P^1`: `χ(O(n)) = dim H^0 - dim H^1`. -/
noncomputable def eulerCharP1 (k : Type) [Field k] (n : ℤ) : ℤ :=
  (Module.finrank k (SheafCohomology.H0 k n) : ℤ) -
  (Module.finrank k (SheafCohomology.H1 k n) : ℤ)

/-- Genus of a smooth plane curve of degree `d`: `g = (d - 1)(d - 2)/2`, the adjunction formula. -/
def genus_plane_curve (d : ℕ) : ℕ := (d - 1) * (d - 2) / 2

end GrothendieckBirkhoff
