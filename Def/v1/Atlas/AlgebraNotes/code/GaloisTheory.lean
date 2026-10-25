/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/GaloisTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.v1.Atlas.AlgebraNotes.code.GaloisTheory


namespace GaloisTheory

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

noncomputable def fundamentalTheoremSymmetricPolynomials
    (σ : Type*) (R : Type*) {n : ℕ} [Fintype σ] [CommRing R]
    (hn : Fintype.card σ = n) :
    MvPolynomial (Fin n) R ≃ₐ[R] ↥(MvPolynomial.symmetricSubalgebra σ R) :=
  MvPolynomial.esymmAlgEquiv σ R hn

end GaloisTheory
