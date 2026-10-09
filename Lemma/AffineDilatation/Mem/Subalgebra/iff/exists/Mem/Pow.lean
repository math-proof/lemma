import Mathlib
import Lemma.AffineDilatation.Basic
import sympy.Basic

open AffineDilatation

/--
[AffineDilatation_mem_subalgebra_iff_exists_mem_pow](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AffineDilatation_mem_subalgebra_iff_exists_mem_pow.lean)
-/

private def den
  {A : Type u} [CommRing A] (a : A) (n : ℕ) : Submonoid.powers a :=
  ⟨a ^ n, n, rfl⟩

private lemma den_add
  {A : Type u} [CommRing A] (a : A) (m n : ℕ) :
  den a (m + n) = den a m * den a n :=
  Subtype.ext (pow_add a m n)

private lemma den_zero
  {A : Type u} [CommRing A] (a : A) :
  den a 0 = 1 :=
  Subtype.ext (pow_zero a)

private lemma den_one
  {A : Type u} [CommRing A] (a : A) :
  den a 1 = ⟨a, Submonoid.mem_powers a⟩ :=
  Subtype.ext (pow_one a)

private noncomputable def frac
  {A : Type u} [CommRing A] (a : A) (n : ℕ) (g : A) : Localization.Away a :=
  IsLocalization.mk' (Localization.Away a) g (den a n)

private lemma frac_zero_right
  {A : Type u} [CommRing A] (a g : A) :
  frac a 0 g = algebraMap A (Localization.Away a) g := by
  rw [frac, den_zero, IsLocalization.mk'_one]

private lemma frac_eq_mul
  {A : Type u} [CommRing A] (a : A) (n : ℕ) (g : A) :
  frac a n g = algebraMap A (Localization.Away a) g * frac a n 1 :=
  IsLocalization.mk'_eq_mul_mk'_one g (den a n)

private lemma frac_add_num
  {A : Type u} [CommRing A] (a : A) (n : ℕ) (g h : A) :
  frac a n (g + h) = frac a n g + frac a n h := by
  rw [frac_eq_mul, map_add, add_mul, ← frac_eq_mul, ← frac_eq_mul]

private lemma frac_add
  {A : Type u} [CommRing A] (a : A) (m n : ℕ) (g h : A) :
  frac a m g + frac a n h = frac a (m + n) (g * a ^ n + h * a ^ m) := by
  rw [frac, frac, frac, ← IsLocalization.mk'_add, den_add]
  rfl

private lemma frac_mul
  {A : Type u} [CommRing A] (a : A) (m n : ℕ) (g h : A) :
  frac a m g * frac a n h = frac a (m + n) (g * h) := by
  rw [frac, frac, frac, ← IsLocalization.mk'_mul, den_add]

private lemma frac_mem_of_mem_pow
  {A : Type u} [CommRing A] (I : Ideal A) (a : A) :
  ∀ (n : ℕ) (g : A), g ∈ I ^ n → frac a n g ∈ subalgebra I a := by
  intro n
  induction n with
  | zero =>
      intro g _
      rw [frac_zero_right]
      exact Subalgebra.algebraMap_mem _ g
  | succ n ih =>
      intro g hg
      rw [pow_succ] at hg
      refine Submodule.mul_induction_on hg ?_ ?_
      ·
        intro x hx y hy
        rw [← frac_mul]
        refine Subalgebra.mul_mem _ (ih x hx) ?_
        rw [frac, den_one]
        exact gen_subset I a ⟨y, hy, rfl⟩
      ·
        intro x y hx hy
        rw [frac_add_num]
        exact Subalgebra.add_mem _ hx hy

private lemma exists_pow_of_mem
  {A : Type u} [CommRing A] (I : Ideal A) (a : A) (ha : a ∈ I) (x : Localization.Away a)
  (hx : x ∈ subalgebra I a) :
  ∃ n : ℕ, ∃ g ∈ I ^ n, frac a n g = x := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      refine ⟨1, g, by simpa using hg, ?_⟩
      rw [frac, den_one]
  | algebraMap r =>
      exact ⟨0, r, by simp, frac_zero_right a r⟩
  | add x y _ _ ihx ihy =>
      obtain ⟨m, g, hg, rfl⟩ := ihx
      obtain ⟨n, h, hh, rfl⟩ := ihy
      refine ⟨m + n, g * a ^ n + h * a ^ m, ?_, (frac_add a m n g h).symm⟩
      refine Ideal.add_mem _ ?_ ?_
      ·
        rw [pow_add]
        exact Ideal.mul_mem_mul hg (Ideal.pow_mem_pow ha n)
      ·
        rw [add_comm, pow_add]
        exact Ideal.mul_mem_mul hh (Ideal.pow_mem_pow ha m)
  | mul x y _ _ ihx ihy =>
      obtain ⟨m, g, hg, rfl⟩ := ihx
      obtain ⟨n, h, hh, rfl⟩ := ihy
      refine ⟨m + n, g * h, ?_, (frac_mul a m n g h).symm⟩
      rw [pow_add]
      exact Ideal.mul_mem_mul hg hh

@[path]
private lemma main
  {A : Type u} [CommRing A]
  {I : Ideal A} {a : A}
-- given
  (ha : a ∈ I)
  (x : Localization.Away a) :
-- imply
  x ∈ AffineDilatation.subalgebra I a ↔
    ∃ n : ℕ, ∃ g : A, g ∈ I ^ n ∧
      IsLocalization.mk' (Localization.Away a) g (⟨a ^ n, n, rfl⟩ : Submonoid.powers a) = x := by
-- proof
  constructor
  ·
    intro hx
    exact exists_pow_of_mem I a ha x hx
  ·
    rintro ⟨n, g, hg, hx⟩
    subst hx
    exact frac_mem_of_mem_pow I a n g hg

-- created on 2026-10-09
