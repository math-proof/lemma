import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Lemma.Int.P2MUtil


namespace Definitions
end Definitions
open Definitions
open CerednikDrinfeld.Omega Polynomial
open scoped Polynomial
open Int


/--
[CerednikDrinfeld_Omega_RatPair_exists_isPoleFreeOn_le_and_degree_lt_and_evalAt_eq_add](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_Omega_RatPair_exists_isPoleFreeOn_le_and_degree_lt_and_evalAt_eq_add.lean)
-/
@[path]
private lemma main
  [Field K] [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
  {Q : RatPair K}
  {t₀ π₀ : K}
-- given
  (_hπ₀ : π₀ ≠ 0) :
-- imply
  ∃ A B : RatPair K,
      A.IsPoleFreeOn ({z | Q.den.eval z ≠ 0} ∪ {z | Valued.v π₀ ≤ Valued.v (z - t₀)}) ∧
      A.num.degree < A.den.degree ∧
      B.IsPoleFreeOn ({z | Q.den.eval z ≠ 0} ∪ {z | Valued.v (z - t₀) < Valued.v π₀}) ∧
      ∀ z : K, Q.den.eval z ≠ 0 → Q.evalAt z = A.evalAt z + B.evalAt z := by
  classical
  by_cases hden : Q.den = 0
  ·
    refine ⟨RatPair.const 0, RatPair.const 0, RatPair.isPoleFreeOn_const _ _, ?_,
      RatPair.isPoleFreeOn_const _ _, ?_⟩
    ·
      show (Polynomial.C (0 : K)).degree < (1 : K[X]).degree
      simp [C_0, degree_zero, degree_one]
    ·
      intro z hz
      exact absurd (by rw [hden, eval_zero]) hz
  obtain ⟨Din, hDin⟩ : ∃ Din : K[X],
      Din = ((Q.den.roots.filter fun c => Valued.v (c - t₀) < Valued.v π₀).map fun a => X - C a).prod := ⟨_, rfl⟩
  obtain ⟨Dout, hDout⟩ : ∃ Dout : K[X],
      Dout = C Q.den.leadingCoeff *
        ((Q.den.roots.filter fun c => ¬ Valued.v (c - t₀) < Valued.v π₀).map fun a => X - C a).prod := ⟨_, rfl⟩
  have hD : Q.den = Din * Dout := by
-- proof
    have h := C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.card_roots_eq_natDegree (p := Q.den))
    rw [← Multiset.filter_add_not (fun c => Valued.v (c - t₀) < Valued.v π₀) Q.den.roots, Multiset.map_add,
      Multiset.prod_add] at h
    rw [hDin, hDout]
    calc
      _ = C Q.den.leadingCoeff *
          (((Q.den.roots.filter fun c => Valued.v (c - t₀) < Valued.v π₀).map fun a => X - C a).prod *
            ((Q.den.roots.filter fun a => ¬ Valued.v (a - t₀) < Valued.v π₀).map fun a => X - C a).prod) := h.symm
      _ = _ := by ring
  have hDin_monic : Din.Monic := by
    rw [hDin]
    exact monic_multiset_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)
  have hlc : Q.den.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hden
  have evprod : ∀ (s : Multiset K) (z : K), ((s.map fun a => X - C a).prod).eval z = (s.map fun a => z - a).prod := by
    intro s z
    rw [eval_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    simp
  have hDin_ne : ∀ z : K, Valued.v π₀ ≤ Valued.v (z - t₀) → Din.eval z ≠ 0 := by
    intro z hz
    rw [hDin, evprod, Ne, Multiset.prod_eq_zero_iff, Multiset.mem_map]
    rintro ⟨a, ha, h0⟩
    rw [Multiset.mem_filter] at ha
    have hza : z = a := (sub_eq_zero.mp h0)
    subst hza
    exact absurd ha.2 (not_lt.mpr hz)
  have hDout_ne : ∀ z : K, Valued.v (z - t₀) < Valued.v π₀ → Dout.eval z ≠ 0 := by
    intro z hz
    rw [hDout, eval_mul, eval_C, evprod]
    refine mul_ne_zero hlc ?_
    rw [Ne, Multiset.prod_eq_zero_iff, Multiset.mem_map]
    rintro ⟨a, ha, h0⟩
    rw [Multiset.mem_filter] at ha
    have hza : z = a := (sub_eq_zero.mp h0)
    subst hza
    exact ha.2 hz
  have hD_ne : ∀ z : K, Q.den.eval z ≠ 0 → Din.eval z ≠ 0 ∧ Dout.eval z ≠ 0 := by
    intro z h
    rw [hD, eval_mul] at h
    exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
  have hcop : IsCoprime Din Dout := by
    rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := K) (K := K)]
    intro a
    simp only [coe_aeval_eq_eval]
    if ha : Valued.v (a - t₀) < Valued.v π₀ then
    exact Or.inr (hDout_ne a ha)
    else
    exact Or.inl (hDin_ne a (not_lt.mp ha))
  obtain ⟨U, W, hUW⟩ := hcop
  have hρq : (modByMonic (Q.num * W) Din) + Din * ((divByMonic (Q.num * W) Din)) = Q.num * W := modByMonic_add_div _ _
  refine ⟨⟨(modByMonic (Q.num * W) Din), Din⟩, ⟨Q.num * U + (divByMonic (Q.num * W) Din) * Dout, Dout⟩, ?_, ?_, ?_, ?_⟩
  ·
    rintro z (hz | hz)
    · exact (hD_ne z hz).1
    · exact hDin_ne z hz
  · exact degree_modByMonic_lt _ hDin_monic
  ·
    rintro z (hz | hz)
    · exact (hD_ne z hz).2
    · exact hDout_ne z hz
  ·
    intro z hz
    obtain ⟨h1, h2⟩ := hD_ne z hz
    have key : (modByMonic (Q.num * W) Din) * Dout + (Q.num * U + (divByMonic (Q.num * W) Din) * Dout) * Din = Q.num := calc
      _ = Dout * ((modByMonic (Q.num * W) Din) + Din * ((divByMonic (Q.num * W) Din))) + Q.num * (U * Din) := by ring
      _ = Dout * (Q.num * W) + Q.num * (U * Din) := by rw [hρq]
      _ = Q.num * (U * Din + W * Dout) := by ring
      _ = Q.num := by rw [hUW, mul_one]
    have keyz := congrArg (eval z) key
    simp only [eval_add, eval_mul] at keyz
    have hdz : Q.den.eval z = Din.eval z * Dout.eval z := by rw [hD, eval_mul]
    simp only [RatPair.evalAt]
    rw [hdz, div_add_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) (mul_ne_zero h1 h2)]
    simp only [eval_add, eval_mul]
    linear_combination (-(Din.eval z * Dout.eval z)) * keyz


-- created on 2026-10-24
