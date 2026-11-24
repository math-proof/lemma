module
public import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalBundleGeneral
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalBundleGeneral
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalSheafDef
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.TwistSheaf
public import Abbrev.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafDef.Part2
public import Def.v1.Atlas.AlgebraicGeometryI.code.TwistSheaf.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalBundleProjective.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open KaehlerDifferential Module CanonicalSheafDef

universe u

section KahlerMvPolynomial

variable (k : Type u) [Field k] (n : ℕ)

/-- Abbreviation for the polynomial ring `k[x₀, …, x_n]` over `k` in `n + 1` variables. -/
abbrev PolyRing := MvPolynomial (Fin (n + 1)) k

end KahlerMvPolynomial
end
