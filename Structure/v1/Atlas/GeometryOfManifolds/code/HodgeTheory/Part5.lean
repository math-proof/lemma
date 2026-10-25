/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Theorem.v1.Atlas.GeometryOfManifolds.code.HodgeTheory
set_option autoImplicit false

open DifferentialFormSpace


/-- The Hodge bigrading on an almost-complex manifold of complex dimension $n$:
a decomposition $\Omega^k = \bigoplus_{p+q=k} \Omega^{p,q}$ with the Hodge star
acting as $* : \Omega^{p,q} \to \Omega^{n-q, n-p}$. -/
structure HasBigrading
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (J : AlmostComplexStr (inst := inst))
    (n : ℕ) where
  Ω_pq : ℕ → ℕ → Type*
  incl : ∀ (p q : ℕ), Ω_pq p q → Ω (p + q)
  incl_injective : ∀ (p q : ℕ), Function.Injective (incl p q)
  pq_add : ∀ (p q : ℕ), Ω_pq p q → Ω_pq p q → Ω_pq p q
  incl_add : ∀ (p q : ℕ) (α β : Ω_pq p q),
    incl p q (pq_add p q α β) = incl p q α + incl p q β
  pq_zero : ∀ (p q : ℕ), Ω_pq p q
  incl_zero : ∀ (p q : ℕ), incl p q (pq_zero p q) = 0
  incl_cast : ∀ {p₁ q₁ p₂ q₂ : ℕ} (hp : p₁ = p₂) (hq : q₁ = q₂)
      (α : Ω_pq p₁ q₁),
      incl p₂ q₂ (cast (by rw [hp, hq]) α) =
        cast (congrArg Ω (by omega)) (incl p₁ q₁ α)
  star_total : ∀ {k : ℕ}, k ≤ 2 * n → Ω k → Ω (2 * n - k)
  star_abc_decomp : ∀ {p' q' : ℕ} (hp' : p' ≤ n) (hq' : q' ≤ n) (β : Ω_pq p' q'),
    ∃ (a b c : ℕ) (ha : a + c = p') (hb : b + c = q') (habc : a + b + c ≤ n),
      ∃ γ : Ω_pq (a + (n - a - b - c)) (b + (n - a - b - c)),
        incl (a + (n - a - b - c)) (b + (n - a - b - c)) γ =
          cast (congrArg Ω (by omega))
            (star_total (by omega : p' + q' ≤ 2 * n) (incl p' q' β))


/-- Data witnessing that on a Kähler manifold, $\bar\square$ and $\Delta$ preserve the
$(p,q)$ bigrading, and that every harmonic form decomposes into harmonic $(p,q)$-components. -/
structure KahlerBigradedData
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : Codifferential (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    (dol_lap : DolbeaultLaplacian dol cod)
    {J : AlmostComplexStr (inst := inst)}
    {n : ℕ}
    (bg : HasBigrading J n) where
  box_bar_preserves_bidegree :
    ∀ (k p' q' : ℕ) (h : p' + q' = k + 1) (ω : bg.Ω_pq p' q'),
      ∃ ω' : bg.Ω_pq p' q',
        cast (congrArg Ω h) (bg.incl p' q' ω') =
          dol_lap.box_bar (cast (congrArg Ω h) (bg.incl p' q' ω))


  laplacian_preserves_bidegree :
    ∀ (k p' q' : ℕ) (h : p' + q' = k + 1) (ω : bg.Ω_pq p' q'),
      ∃ ω' : bg.Ω_pq p' q',
        cast (congrArg Ω h) (bg.incl p' q' ω') =
          laplacian cod (cast (congrArg Ω h) (bg.incl p' q' ω))

  harmonic_bigrading_decomposition :
    ∀ {k : ℕ} (h_form : Ω (k + 1)) (_h_harmonic : laplacian cod h_form = 0),
      ∃ (component : Fin (k + 2) → Ω (k + 1)),
        (∀ (j : Fin (k + 2)),
          ∃ (ω : bg.Ω_pq j.val (k + 1 - j.val)),
            cast (congrArg Ω (Nat.add_sub_cancel' (Nat.lt_succ_iff.mp j.isLt)))
              (bg.incl j.val (k + 1 - j.val) ω) = component j) ∧
        (∀ j, dol.del (component j) = 0) ∧
        (∀ j, dol.delbar (component j) = 0) ∧
        (∀ j, laplacian cod (component j) = 0) ∧
        h_form = Finset.univ.sum component


