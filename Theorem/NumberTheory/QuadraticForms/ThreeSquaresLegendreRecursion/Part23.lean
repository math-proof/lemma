/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.NumberTheory.LegendreSymbol.Basic
import Def.NumberTheory.QuadraticForms.ThreeSquares
import Lemma.Nat.QuadraticForms.ThreeSquares
import Mathlib.Algebra.Quaternion
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.FieldTheory.Finite.Basic
import Def.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part25


namespace MetaMathlibExt

lemma r3leg_rep_rec {p n k : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) :
    (Nat.threeSquareRepresentationCount (p ^ (2 * (k + 2)) * n) : ℤ) =
      ((p : ℤ) + 1) *
          Nat.threeSquareRepresentationCount (p ^ (2 * (k + 1)) * n) -
        (p : ℤ) * Nat.threeSquareRepresentationCount (p ^ (2 * k) * n) := by
  have hfactor : p ^ (2 * (k + 1)) * n = p ^ 2 * (p ^ (2 * k) * n) := by
    rw [show 2 * (k + 1) = 2 + 2 * k by omega, pow_add]
    ring
  have hnext : p ^ 2 * (p ^ (2 * (k + 1)) * n) = p ^ (2 * (k + 2)) * n := by
    rw [show 2 * (k + 2) = 2 + 2 * (k + 1) by omega, pow_add]
    ring
  have hdiv : p ^ 2 ∣ p ^ (2 * (k + 1)) * n := ⟨p ^ (2 * k) * n, hfactor⟩
  have hp2pos : 0 < p ^ 2 := pow_pos (Fact.out : Nat.Prime p).pos 2
  have hquot : (p ^ (2 * (k + 1)) * n) / p ^ 2 = p ^ (2 * k) * n := by
    rw [hfactor, Nat.mul_div_cancel_left _ hp2pos]
  have hpdiv : p ∣ p ^ (2 * (k + 1)) * n :=
    dvd_trans (⟨p, by simp [pow_two]⟩ : p ∣ p ^ 2) hdiv
  have hmzero : ((p ^ (2 * (k + 1)) * n : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hpdiv
  have hleg : legendreSym p (-((p ^ (2 * (k + 1)) * n : ℕ) : ℤ)) = 0 := by
    apply (legendreSym.eq_zero_iff p _).mpr
    rw [Int.cast_neg, Int.cast_natCast, hmzero, neg_zero]
  have h := r3leg_alpha_one (n := p ^ (2 * (k + 1)) * n) hp3
  rw [hnext, hleg, ite_eq_left hdiv, hquot] at h
  simpa using h

lemma r3leg_formula {p n α : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) :
    (Nat.threeSquareRepresentationCount (p ^ (2 * α) * n) : ℤ) =
      (r3legG p (α + 1) - legendreSym p (-(n : ℤ)) * r3legG p α) *
          Nat.threeSquareRepresentationCount n -
        (p : ℤ) * r3legG p α *
          (if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0) := by
  let P : ℕ → Prop := fun a =>
    (Nat.threeSquareRepresentationCount (p ^ (2 * a) * n) : ℤ) =
      (r3legG p (a + 1) - legendreSym p (-(n : ℤ)) * r3legG p a) *
          Nat.threeSquareRepresentationCount n -
        (p : ℤ) * r3legG p a *
          (if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0)
  change P α
  apply Nat.twoStepInduction (motive := P)
  · dsimp [P]
    rw [r3leg_g_zero hp3, r3leg_g_one hp3]
    simp
  · dsimp [P]
    rw [r3leg_g_one hp3, r3leg_g_two hp3]
    simpa using r3leg_alpha_one (n := n) hp3
  · intro k hk hk1
    dsimp [P] at hk hk1 ⊢
    rw [r3leg_rep_rec hp3, hk1, hk]
    have hg0 := r3leg_g_rec (p := p) (k := k) hp3
    have hg1 := r3leg_g_rec (p := p) (k := k + 1) hp3
    rw [hg1, hg0]
    ring

/--
Legendre-symbol recursion for the sums-of-three-squares function (cf. Hsquare).

Source: Liuquan Wang, "Another Proof of a Conjecture by Hirschhorn and Sellers on Overpartitions", Journal of Integer Sequences 17 (2014), Article 14.9.8, Lemma `r3relation`, lines 228-232, <https://cs.uwaterloo.ca/journals/JIS/VOL17/Wang2/wang15.tex>.

Proves `Wanted` entry `r3_legendre_recursion`.

Proof: The route is an elementary p-neighbour double count using quaternionic descent and
finite-field conic counts, followed by a two-step induction on the exponent.
-/
theorem r3_legendre_recursion
    {p n α : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) (hn : 1 ≤ n) :
    (Nat.threeSquareRepresentationCount (p ^ (2 * α) * n) : ℤ) =
      (((((p : ℤ) ^ (α + 1) - 1) / ((p : ℤ) - 1)) -
          legendreSym p (-(n : ℤ)) *
            (((p : ℤ) ^ α - 1) / ((p : ℤ) - 1))) *
          Nat.threeSquareRepresentationCount n -
        (p : ℤ) * (((p : ℤ) ^ α - 1) / ((p : ℤ) - 1)) *
          (if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0)) := by
  simpa [r3legG] using r3leg_formula (p := p) (n := n) (α := α) hp3

end MetaMathlibExt
