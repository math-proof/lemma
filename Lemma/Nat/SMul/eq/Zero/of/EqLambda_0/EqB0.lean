import Mathlib
import sympy.Basic
import Lemma.CerednikDrinfeld.GradedCartierModuleData
import Lemma.CerednikDrinfeld.GradedCartierNModule
open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData


namespace Definitions
end Definitions

/--
[CerednikDrinfeld_GradedCartierModuleData_nsmul_eq_zero_of_lambda_eq_zero_of_cast_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_GradedCartierModuleData_nsmul_eq_zero_of_lambda_eq_zero_of_cast_eq_zero.lean)
-/
@[path]
private lemma main
  [CommRing B]
  {p : ℕ} [Fact p.Prime]
  {j : CerednikDrinfeld.Zp2 p →+* B}
  {D : CerednikDrinfeld.GradedCartierModuleData p B j}
  {z : D.NMod}
-- given
  (hp : (p : B) = 0)
  (hz : D.lambda z = 0) :
-- imply
  p • z = 0 := by
-- proof
  obtain hB | hB := subsingleton_or_nontrivial B
  ·
    have : Subsingleton (WittVector p B) := ⟨fun a b => WittVector.ext fun n => Subsingleton.elim _ _⟩
    have : z = 0 := by
      rw [← one_smul (WittVector p B) z, Subsingleton.elim (1 : WittVector p B) 0, zero_smul]
    rw [this, nsmul_zero]
  ·
    have : CharP B p := by
      obtain ⟨q, hq⟩ := CharP.exists B
      have hdvd : q ∣ p := (CharP.cast_eq_zero_iff B q p).1 hp
      obtain h1 | h2 := (Nat.dvd_prime (Fact.out : p.Prime)).1 hdvd
      ·
        subst h1
        exact absurd ((CharP.cast_eq_zero_iff B 1 1).2 (dvd_refl 1))
          (Nat.cast_one (R := B) ▸ one_ne_zero)
      ·
        subst h2
        exact hq
    obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective z
    rw [lambda_nMk] at hz
    have hpW : ((p : ℕ) : WittVector p B) = WittVector.verschiebung 1 := by
      ext n
      cases n
      ·
        rw [WittVector.verschiebung_coeff_zero]
        exact WittVector.coeff_p_zero (p := p) (R := B)
      ·
        next n =>
          rw [WittVector.verschiebung_coeff_succ]
          cases n
          ·
            rw [WittVector.coeff_p_one]
            simp
          ·
            next _ =>
              rw [WittVector.coeff_p (p := p) (R := B)]
              simp
    have hpm : (p : ℕ) • m = D.verschiebung (D.frobenius m) := by
      simpa [one_smul, ← hpW, Nat.cast_smul_eq_nsmul] using
        (D.verschiebung_smul_frobenius 1 m).symm
    have hPm : D.varpi (D.frobenius m) = -((p : ℕ) • m') := by
      rw [D.varpi_frobenius, eq_neg_iff_add_eq_zero, ← D.frobenius_verschiebung, ← map_add, hz,
        map_zero]
    rw [← map_nsmul, Prod.smul_mk, hpm]
    have : ((p : ℕ) • m' : D.M) = -D.varpi (D.frobenius m) := by rw [hPm, neg_neg]
    rw [this]
    exact D.nMk_verschiebung_neg_varpi _


-- created on 2026-10-24
