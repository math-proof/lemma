import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.ModularCurve.EisensteinTwoCoeff
import Lemma.Int.P2MUtil
open ModularCurve


/-- ported from external source -/

private lemma filter_divisors_mul_prime {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : n ≠ 0) :
  (n * p).divisors.filter (fun d => ¬ p ∣ d) = n.divisors.filter (fun d => ¬ p ∣ d) := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  ·
    rintro ⟨⟨hd, -⟩, hpd⟩
    exact ⟨⟨((hp.coprime_iff_not_dvd.mpr hpd).symm).dvd_of_dvd_mul_right hd, hn⟩, hpd⟩
  ·
    rintro ⟨⟨hd, -⟩, hpd⟩
    exact ⟨⟨dvd_mul_of_dvd_left hd p, mul_ne_zero hn hp.ne_zero⟩, hpd⟩

private lemma sigmaPrimeTo_mul_self {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : n ≠ 0) :
  sigmaPrimeTo p (n * p) = sigmaPrimeTo p n := by
  simp only [sigmaPrimeTo]
  rw [filter_divisors_mul_prime hp hn]
p2m_open_scoped "ModularCurve" in

private lemma ModularCurve.eisensteinTwoCoeff_mul_level (p : ℕ) [Fact p.Prime] (n : ℕ) : eisensteinTwoCoeff p (n * p) = eisensteinTwoCoeff p n := by
  have hp : p.Prime := Fact.out
  if hn : n = 0 then
    rw [hn, zero_mul]
  else
    rw [eisensteinTwoCoeff_of_ne_zero p (mul_ne_zero hn hp.ne_zero),
      eisensteinTwoCoeff_of_ne_zero p hn, sigmaPrimeTo_mul_self hp hn]
@[path]
private lemma main
  {p : ℕ} [Fact p.Prime]
  {n : ℕ} :
-- imply
  eisensteinTwoCoeff p (n * p) = eisensteinTwoCoeff p n :=
-- proof
  ModularCurve.eisensteinTwoCoeff_mul_level p n


-- created on 2026-10-23
