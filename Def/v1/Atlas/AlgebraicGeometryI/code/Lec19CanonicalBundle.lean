/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec19CanonicalBundle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Def.v1.Atlas.AlgebraicGeometryI.code.PicardProjective.Part7
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.PicardProjective


noncomputable section

open KaehlerDifferential Module PicardProjective

universe u


/-- Definition 37 (Lecture 19). The canonical module `ω = ∧^{d+1} Ω` of the polynomial ring
`k[x_0,…,x_d]`, the algebraic model of the canonical bundle on affine `(d+1)`-space. -/
def canonicalModule (k : Type u) [Field k] (d : ℕ) :
    Submodule (MvPolynomial (Fin (d + 1)) k)
      (ExteriorAlgebra (MvPolynomial (Fin (d + 1)) k) (Ω[MvPolynomial (Fin (d + 1)) k⁄k])) :=
  ⋀[MvPolynomial (Fin (d + 1)) k]^(d + 1) (Ω[MvPolynomial (Fin (d + 1)) k⁄k])

end
