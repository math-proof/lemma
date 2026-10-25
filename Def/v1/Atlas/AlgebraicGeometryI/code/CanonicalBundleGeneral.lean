/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalBundleGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Instance.v1.Atlas.AlgebraicGeometryI.code.CanonicalBundleGeneral


noncomputable section

open KaehlerDifferential Module

universe u

section RankComputation

variable (k : Type u) [Field k] (n : ℕ)

/-- A basis (of cardinality 1) for the top exterior power of Kähler differentials. -/
noncomputable def exteriorPowerKahlerBasis :
    Basis (Fin 1) (MvPolynomial (Fin (n+1)) k)
      (⋀[MvPolynomial (Fin (n+1)) k]^(n+1) (Ω[MvPolynomial (Fin (n+1)) k⁄k])) :=
  ((mvPolynomialBasis k (Fin (n+1))).exteriorPower (n+1)).reindex
    (Fintype.equivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, powersetCard.card, Nat.card_fin, Nat.choose_self]; simp))

/-- Linear equivalence between the canonical bundle of `A^{n+1}_k` and the structure sheaf
(rank-one free module), arising from the chosen basis. -/
noncomputable def canonicalBundleLinearEquiv :
    (⋀[MvPolynomial (Fin (n+1)) k]^(n+1) (Ω[MvPolynomial (Fin (n+1)) k⁄k]))
      ≃ₗ[MvPolynomial (Fin (n+1)) k] (Fin 1 → MvPolynomial (Fin (n+1)) k) :=
  (exteriorPowerKahlerBasis k n).equivFun

end RankComputation
end
