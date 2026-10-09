import Mathlib
import sympy.Basic


/--
[CerednikDrinfeld_apply_apply_sub_apply_add_smul_eq_zero_of_reduction](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_apply_apply_sub_apply_add_smul_eq_zero_of_reduction.lean)
-/
@[path]
private lemma main
  {J P : Type*} [AddCommGroup J] [AddCommGroup P]
  {D : AddSubgroup J}
  {g T : J → J}
  {red : J → P}
  {F V : P →+ P}
  {ℓ : ℕ}
-- given
  (hg : ∀ t ∈ D, g t ∈ D)
  (hT : ∀ t ∈ D, T t ∈ D)
  (hadd : ∀ x ∈ D, ∀ y ∈ D, red (x + y) = red x + red y)
  (hinj : ∀ x ∈ D, red x = 0 → x = 0)
  (hgal : ∀ t ∈ D, red (g t) = F (red t))
  (hhecke : ∀ t ∈ D, red (T t) = F (red t) + V (red t))
  (hVF : ∀ t ∈ D, V (F (red t)) = ℓ • red t) :
-- imply
  ∀ t ∈ D, g (g t) - T (g t) + ℓ • t = 0 := by
-- proof
  intro t ht
  have hgt := hg t ht
  have hneg : ∀ x ∈ D, red (-x) = -red x := by
    intro x hx
    have h0 : red 0 = 0 := by
      have := hadd 0 D.zero_mem 0 D.zero_mem
      rwa [add_zero, left_eq_add] at this
    have := hadd x hx (-x) (D.neg_mem hx)
    rw [add_neg_cancel, h0] at this
    exact (neg_eq_of_add_eq_zero_right this.symm).symm
  have hsmul : ∀ (n : ℕ) (x : J), x ∈ D → red (n • x) = n • red x := by
    intro n x hx
    induction n with
    | zero =>
      have := hadd 0 D.zero_mem 0 D.zero_mem
      rw [add_zero, left_eq_add] at this
      simpa using this
    | succ n ih => rw [succ_nsmul, succ_nsmul, hadd _ (D.nsmul_mem hx n) _ hx, ih]
  apply hinj _ (D.add_mem (D.sub_mem (hg _ hgt) (hT _ hgt)) (D.nsmul_mem ht ℓ))
  rw [hadd _ (D.sub_mem (hg _ hgt) (hT _ hgt)) _ (D.nsmul_mem ht ℓ), sub_eq_add_neg,
    hadd _ (hg _ hgt) _ (D.neg_mem (hT _ hgt)), hneg _ (hT _ hgt), hsmul ℓ t ht,
    hgal _ hgt, hhecke _ hgt, hgal _ ht, ← hVF t ht]
  abel


-- created on 2026-10-05
