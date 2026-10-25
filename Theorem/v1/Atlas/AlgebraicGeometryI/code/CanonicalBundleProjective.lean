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
import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalBundleProjective


noncomputable section

open KaehlerDifferential Module CanonicalSheafDef

universe u

section KahlerMvPolynomial

variable (k : Type u) [Field k] (n : ℕ)

/-- The rank of the Kähler differential module of `k[x₀,…,x_n]` is `n + 1`. -/
theorem kahler_mvPolynomial_finrank :
    Module.finrank (PolyRing k n) (Ω[PolyRing k n⁄k]) = n + 1 := by
  rw [Module.finrank_eq_card_basis (kahlerBasis_mvPolynomial k n), Fintype.card_fin]

end KahlerMvPolynomial
end
