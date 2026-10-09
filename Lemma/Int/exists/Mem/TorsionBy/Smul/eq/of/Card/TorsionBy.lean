import Mathlib
import sympy.Basic

open Module Submodule Function


structure Pres (M : Type*) [AddCommGroup M] (n : ℕ) (V : Type*) [AddCommGroup V] where
  ι : V →+ M
  hι : Function.Injective ι
  hιr : ∀ x : M, x ∈ ι.range ↔ ((n : ℕ) : ℤ) • x = 0

/--
[AddCommGroup_exists_mem_torsionBy_smul_eq_of_card_torsionBy](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AddCommGroup_exists_mem_torsionBy_smul_eq_of_card_torsionBy.lean)
-/

noncomputable def equiv
  {M : Type*}
  [AddCommGroup M]
  {n : ℕ}
  {V : Type*}
  [AddCommGroup V]
  (P : Pres M n V) : V ≃ torsionBy ℤ M ((n : ℕ) : ℤ) :=
  Equiv.ofBijective
    (fun v => ⟨P.ι v, (mem_torsionBy_iff _ _).2 ((P.hιr _).1 ⟨v, rfl⟩)⟩)
    ⟨fun v w h => P.hι (Subtype.ext_iff.1 h), fun x => by
      obtain ⟨v, hv⟩ := (P.hιr x.1).2 ((mem_torsionBy_iff _ _).1 x.2)
      exact ⟨v, Subtype.ext hv⟩⟩

def self
  (M : Type*)
  [AddCommGroup M]
  (n : ℕ) : Pres M n (torsionBy ℤ M ((n : ℕ) : ℤ)) where
  ι := (torsionBy ℤ M ((n : ℕ) : ℤ)).subtype.toAddMonoidHom
  hι := Subtype.val_injective
  hιr x := by
    constructor
    · rintro ⟨v, rfl⟩
      exact (mem_torsionBy_iff _ _).1 v.2
    · intro hx
      exact ⟨⟨x, (mem_torsionBy_iff _ _).2 hx⟩, rfl⟩

private lemma  nsmul_mem_torsionBy_pow
    {M : Type*}
    [AddCommGroup M]
    (ℓ m : ℕ)
    {x : M} (hx : x ∈ torsionBy ℤ M ((ℓ ^ (m + 1) : ℕ) : ℤ)) :
    ℓ • x ∈ torsionBy ℤ M ((ℓ ^ m : ℕ) : ℤ) := by
  rw [mem_torsionBy_iff, natCast_zsmul] at hx ⊢
  rwa [← mul_smul, ← pow_succ]

def mulL
  {M : Type*}
  [AddCommGroup M]
  (ℓ m : ℕ)
  : torsionBy ℤ M ((ℓ ^ (m + 1) : ℕ) : ℤ) →ₗ[ℤ] torsionBy ℤ M ((ℓ ^ m : ℕ) : ℤ) where
  toFun x := ⟨ℓ • (x : M), nsmul_mem_torsionBy_pow ℓ m x.2⟩
  map_add' x y := by
    apply Subtype.ext
    change ℓ • ((x : M) + y) = ℓ • (x : M) + ℓ • (y : M)
    exact smul_add ℓ (x : M) y
  map_smul' c x := by
    apply Subtype.ext
    change ℓ • (c • (x : M)) = c • (ℓ • (x : M))
    exact smul_comm ℓ c (x : M)

private lemma  nsmul_ι
  {M : Type*}
  [AddCommGroup M]
  {n : ℕ}
  {V : Type*}
  [AddCommGroup V]
  (P : Pres M n V) (v : V) : n • P.ι v = 0 := by
  have := (P.hιr (P.ι v)).1 ⟨v, rfl⟩
  rwa [natCast_zsmul] at this

private lemma  nsmul_self
  {M : Type*}
  [AddCommGroup M]
  {n : ℕ}
  {V : Type*}
  [AddCommGroup V]
  (P : Pres M n V) (v : V) : n • v = 0 :=
  P.hι (by rw [map_nsmul, nsmul_ι P, map_zero])

private lemma  exists_eq_of_nsmul
  {M : Type*}
  [AddCommGroup M]
  {n : ℕ}
  {V : Type*}
  [AddCommGroup V]
  (P : Pres M n V) {x : M} (hx : n • x = 0) : ∃ v, P.ι v = x := by
  obtain ⟨v, hv⟩ := (P.hιr x).2 (by rwa [natCast_zsmul])
  exact ⟨v, hv⟩

private lemma  mem_torsionBy
  {M : Type*}
  [AddCommGroup M]
  {n : ℕ}
  {V : Type*}
  [AddCommGroup V]
  (P : Pres M n V) (v : V) : P.ι v ∈ torsionBy ℤ M ((n : ℕ) : ℤ) :=
  (mem_torsionBy_iff _ _).2 ((P.hιr _).1 ⟨v, rfl⟩)

private lemma  natCard_eq
  {M : Type*}
  [AddCommGroup M]
  {n : ℕ}
  {V : Type*}
  [AddCommGroup V]
  (P : Pres M n V) : Nat.card V = Nat.card (torsionBy ℤ M ((n : ℕ) : ℤ)) :=
  Nat.card_congr (equiv P)


@[simp] theorem coe_mulL
    {M : Type*}
    [AddCommGroup M]
    (ℓ m : ℕ)
    (x : torsionBy ℤ M ((ℓ ^ (m + 1) : ℕ) : ℤ)) :
    ((mulL ℓ m x : torsionBy ℤ M ((ℓ ^ m : ℕ) : ℤ)) : M) = ℓ • (x : M) := rfl

private lemma  natCard_ker_mulL
    {M : Type*}
    [AddCommGroup M]
    (ℓ m : ℕ)
    :
    Nat.card (LinearMap.ker (mulL (M := M) ℓ m)) =
      Nat.card (torsionBy ℤ M ((ℓ ^ 1 : ℕ) : ℤ)) := by
  refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨x.1.1, ?_⟩) ⟨?_, ?_⟩)
  · have hx := x.2
    rw [LinearMap.mem_ker, Subtype.ext_iff, coe_mulL] at hx
    rw [mem_torsionBy_iff, natCast_zsmul, pow_one]
    exact hx
  · intro x y h
    exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h))
  · rintro ⟨y, hy⟩
    rw [mem_torsionBy_iff, natCast_zsmul, pow_one] at hy
    have hy' : y ∈ torsionBy ℤ M ((ℓ ^ (m + 1) : ℕ) : ℤ) := by
      rw [mem_torsionBy_iff, natCast_zsmul, pow_succ, mul_smul, hy, smul_zero]
    refine ⟨⟨⟨y, hy'⟩, ?_⟩, rfl⟩
    rw [LinearMap.mem_ker, Subtype.ext_iff, coe_mulL]
    exact hy

private lemma  mulL_surjective
    {M : Type*}
    [AddCommGroup M]
    (ℓ m : ℕ)
    (r : ℕ)
    (hℓ : 0 < ℓ)
    (h1 : Nat.card (torsionBy ℤ M ((ℓ ^ 1 : ℕ) : ℤ)) = (ℓ ^ 1) ^ r)
    (hm : Nat.card (torsionBy ℤ M ((ℓ ^ m : ℕ) : ℤ)) = (ℓ ^ m) ^ r)
    (hm1 : Nat.card (torsionBy ℤ M ((ℓ ^ (m + 1) : ℕ) : ℤ)) = (ℓ ^ (m + 1)) ^ r) :
    Surjective (mulL (M := M) ℓ m) := by
  set f := mulL (M := M) ℓ m with hf
  have hℓ0 : ℓ ≠ 0 := hℓ.ne'
  haveI hfin1 : Finite (torsionBy ℤ M ((ℓ ^ (m + 1) : ℕ) : ℤ)) :=
    Nat.finite_of_card_ne_zero (by rw [hm1]; positivity)
  haveI hfin0 : Finite (torsionBy ℤ M ((ℓ ^ m : ℕ) : ℤ)) :=
    Nat.finite_of_card_ne_zero (by rw [hm]; positivity)

  have hmul := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  rw [Nat.card_congr f.quotKerEquivRange.toEquiv, hm1, natCard_ker_mulL, h1] at hmul

  have hrange : Nat.card (LinearMap.range f) = (ℓ ^ m) ^ r := by
    have h : (ℓ ^ 1) ^ r * Nat.card (LinearMap.range f) = (ℓ ^ 1) ^ r * (ℓ ^ m) ^ r := by
      rw [← hmul, ← mul_pow, pow_one, ← pow_succ']
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h

  have hbij : Bijective (LinearMap.range f).subtype :=
    (LinearMap.range f).injective_subtype.bijective_of_nat_card_le (by rw [hrange, hm])
  intro y
  obtain ⟨⟨z, x, rfl⟩, hz⟩ := hbij.2 y
  exact ⟨x, hz⟩


@[path]
private lemma main
  [AddCommGroup M]
  {ℓ : ℕ} [Fact ℓ.Prime]
  {r m : ℕ}
  {x : M}
-- given
  (hcard : ∀ j ≤ m + 1, Nat.card (Submodule.torsionBy ℤ M ((ℓ ^ j : ℕ) : ℤ)) = (ℓ ^ j) ^ r)
  (hx : x ∈ Submodule.torsionBy ℤ M ((ℓ ^ m : ℕ) : ℤ)) :
-- imply
  ∃ y ∈ Submodule.torsionBy ℤ M ((ℓ ^ (m + 1) : ℕ) : ℤ), ℓ • y = x := by
-- proof
  have hm : m ≤ m + 1 := Nat.le_succ m
  have h1 : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
  obtain ⟨⟨y, hy⟩, hyx⟩ := mulL_surjective ℓ m r (Fact.out : ℓ.Prime).pos (hcard 1 h1)
    (hcard m hm) (hcard (m + 1) le_rfl) ⟨x, hx⟩
  exact ⟨y, hy, Subtype.ext_iff.1 hyx⟩


-- created on 2026-10-09
