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
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.CanonicalBundleProjective


noncomputable section

open KaehlerDifferential Module CanonicalSheafDef

universe u

section KahlerMvPolynomial

variable (k : Type u) [Field k] (n : ℕ)

/-- Canonical basis of `Ω[k[x₀,…,x_n]⁄k]` given by the `dxᵢ`. -/
def kahlerBasis_mvPolynomial :
    Basis (Fin (n + 1)) (PolyRing k n) (Ω[PolyRing k n⁄k]) :=
  mvPolynomialBasis k (Fin (n + 1))

end KahlerMvPolynomial
end
