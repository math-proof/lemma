/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part5
set_option autoImplicit false

open DifferentialFormSpace


/-- A linear differential operator $L: \Omega^{p+1} \to \Omega^{p+1}$ of order `order`
equipped with its principal symbol $\sigma_k(L)(\xi)$ that is homogeneous of degree
`order` in $\xi$. -/
structure IsDifferentialOperator
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (L : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)) where
  order : ℕ
  symbol : Ω 1 → (∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1))
  L_add : ∀ {p : ℕ} (α β : Ω (p + 1)), L (α + β) = L α + L β
  L_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω (p + 1)), L (r • α) = r • L α
  symbol_homogeneous : ∀ (r : ℝ) (ξ : Ω 1) {p : ℕ} (α : Ω (p + 1)),
    symbol (r • ξ) α = r ^ order • symbol ξ α

/-- A general elliptic operator $L: \Gamma E \to \Gamma F$: a linear operator
whose principal symbol $\sigma(L)(\xi)$ is a bijection for every nonzero $\xi$. -/
structure IsElliptic
    {ΓE : Type*} {ΓF : Type*} {T : Type*}
    [AddCommGroup ΓE] [Module ℝ ΓE]
    [AddCommGroup ΓF] [Module ℝ ΓF]
    [AddCommGroup T] [Module ℝ T]
    (L : ΓE → ΓF) where
  order : ℕ
  symbol : T → (ΓE → ΓF)
  L_add : ∀ (s t : ΓE), L (s + t) = L s + L t
  L_smul : ∀ (r : ℝ) (s : ΓE), L (r • s) = r • L s
  symbol_homogeneous : ∀ (r : ℝ) (ξ : T) (s : ΓE),
    symbol (r • ξ) s = r ^ order • symbol ξ s
  elliptic : ∀ (ξ : T), ξ ≠ 0 → Function.Bijective (symbol ξ)

/-- An elliptic differential endomorphism $L: \Omega^{p+1} \to \Omega^{p+1}$:
a differential operator whose principal symbol is bijective at every nonzero covector. -/
structure IsEllipticEndo
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (L : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1))
    extends IsDifferentialOperator (inst := inst) L where
  elliptic : ∀ (ξ : Ω 1), ξ ≠ 0 → ∀ {p : ℕ}, Function.Bijective (symbol ξ (p := p))


