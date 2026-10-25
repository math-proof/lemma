/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalBundleProjective.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalBundleGeneral
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalBundleGeneral
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalSheafDef
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.TwistSheaf
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafDef.Part2
import Def.v1.Atlas.AlgebraicGeometryI.code.TwistSheaf.Part2
import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalBundleProjective.Part2


noncomputable section

open KaehlerDifferential Module CanonicalSheafDef

universe u

section MvPolynomialSmooth

variable (k : Type u) [Field k] (n : ℕ)

/-- A polynomial ring `k[x₀, …, x_n]` is smooth of dimension `n + 1` over `k`. -/
instance polyRing_isSmoothOfDimension :
    IsSmoothOfDimension k (PolyRing k n) (n + 1) where
  free := inferInstance
  finite := Module.Finite.of_basis (kahlerBasis_mvPolynomial k n)
  finrank_eq := kahler_mvPolynomial_finrank k n

end MvPolynomialSmooth
end
