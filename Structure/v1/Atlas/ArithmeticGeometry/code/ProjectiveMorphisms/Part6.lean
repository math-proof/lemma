/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveMorphisms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties.Part7
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.ProjectiveVarieties
import Mathlib.Algebra.MvPolynomial.Monad
import Def.v1.Atlas.ArithmeticGeometry.code.ProjectiveMorphisms.Part5


noncomputable section

open MvPolynomial

open scoped LinearAlgebra.Projectivization

namespace ProjectiveThm1518

open MvPolynomial

open scoped LinearAlgebra.Projectivization

open ProjectiveRegularFunction

open ProjectiveRatMap

variable {m n : ℕ} (k : Type*) [Field k]


/-- Compatibility: for $P \in X$ in the regular domain of $\varphi^* r$, there is a corresponding $Q = \varphi(P) \in Y$ in the regular domain of $r$ such that $(\varphi^* r)(P) = r(Q)$. -/
structure ProjectiveFunctionFieldHom
    (m n : ℕ) (k : Type*) [Field k]
    (X : Set (ℙ k (Fin (m + 1) → k)))
    (Y : Set (ℙ k (Fin (n + 1) → k))) where
  toFun : ProjectiveRatFun n k Y → ProjectiveRatFun m k X
  map_eq : ∀ (r₁ r₂ : ProjectiveRatFun n k Y),
    (∀ P ∈ Y, ∀ (hP₁ : P ∈ r₁.regularDomain k) (hP₂ : P ∈ r₂.regularDomain k),
      r₁.evalAt k P hP₁ = r₂.evalAt k P hP₂) →
    toFun r₁ = toFun r₂
  map_mul_eval : ∀ (r₁ r₂ : ProjectiveRatFun n k Y)
    (r₁r₂ : ProjectiveRatFun n k Y),

    (∀ P ∈ Y, ∀ (hP₁ : P ∈ r₁.regularDomain k) (hP₂ : P ∈ r₂.regularDomain k)
      (hP₁₂ : P ∈ r₁r₂.regularDomain k),
      r₁r₂.evalAt k P hP₁₂ = r₁.evalAt k P hP₁ * r₂.evalAt k P hP₂) →
    ∀ P ∈ X,
    ∀ (hPθ₁ : P ∈ (toFun r₁).regularDomain k)
      (hPθ₂ : P ∈ (toFun r₂).regularDomain k)
      (hPθ₁₂ : P ∈ (toFun r₁r₂).regularDomain k),
    (toFun r₁r₂).evalAt k P hPθ₁₂ =
      (toFun r₁).evalAt k P hPθ₁ * (toFun r₂).evalAt k P hPθ₂
  map_add_eval : ∀ (r₁ r₂ : ProjectiveRatFun n k Y)
    (r₁r₂ : ProjectiveRatFun n k Y),

    (∀ P ∈ Y, ∀ (hP₁ : P ∈ r₁.regularDomain k) (hP₂ : P ∈ r₂.regularDomain k)
      (hP₁₂ : P ∈ r₁r₂.regularDomain k),
      r₁r₂.evalAt k P hP₁₂ = r₁.evalAt k P hP₁ + r₂.evalAt k P hP₂) →
    ∀ P ∈ X,
    ∀ (hPθ₁ : P ∈ (toFun r₁).regularDomain k)
      (hPθ₂ : P ∈ (toFun r₂).regularDomain k)
      (hPθ₁₂ : P ∈ (toFun r₁r₂).regularDomain k),
    (toFun r₁r₂).evalAt k P hPθ₁₂ =
      (toFun r₁).evalAt k P hPθ₁ + (toFun r₂).evalAt k P hPθ₂
  map_const_eval : ∀ (c : k) (const_c : ProjectiveRatFun n k Y),

    (∀ P ∈ Y, ∀ (hP : P ∈ const_c.regularDomain k),
      const_c.evalAt k P hP = c) →
    ∀ P ∈ X, ∀ (hP : P ∈ (toFun const_c).regularDomain k),
      (toFun const_c).evalAt k P hP = c

end ProjectiveThm1518
end
