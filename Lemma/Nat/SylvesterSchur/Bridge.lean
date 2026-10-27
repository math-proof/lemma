import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped BigOperators
open Finset Nat


namespace Nat.SylvesterSchur

/--
[prime_dvd_choose_of_dvd_consecutive](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/Bridge.lean)
-/
@[path]
lemma prime_dvd_choose_of_dvd_consecutive
  {n k p j : ℕ}
-- given
  (hp : p.Prime)
  (hp_gt : n < p)
  (hj : j < n)
  (hdvd : p ∣ k + j) :
-- imply
  p ∣ Nat.choose (k + n - 1) n := by
-- proof
  have hprod_eq : k.ascFactorial n = n ! * Nat.choose (k + n - 1) n :=
    Nat.ascFactorial_eq_factorial_mul_choose' k n
  have hprod_eq_range : k.ascFactorial n = ∏ i ∈ Finset.range n, (k + i) :=
    Nat.ascFactorial_eq_prod_range k n
  have hp_dvd_prod : p ∣ ∏ i ∈ Finset.range n, (k + i) :=
    hdvd.trans (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hj))
  rw [← hprod_eq_range, hprod_eq] at hp_dvd_prod
  exact (hp.coprime_factorial_of_lt hp_gt).dvd_of_dvd_mul_left hp_dvd_prod

end Nat.SylvesterSchur

namespace Nat.SylvesterSchur

/--
[exists_dvd_consecutive_of_prime_dvd_choose](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/Bridge.lean)
-/
@[path]
lemma exists_dvd_consecutive_of_prime_dvd_choose
  {n k p : ℕ}
-- given
  (hp : p.Prime)
  (hp_dvd : p ∣ Nat.choose (k + n - 1) n) :
-- imply
  ∃ i < n, p ∣ k + i := by
-- proof
  have hprod_eq : k.ascFactorial n = n ! * Nat.choose (k + n - 1) n :=
    Nat.ascFactorial_eq_factorial_mul_choose' k n
  have hprod_eq_range : k.ascFactorial n = ∏ i ∈ Finset.range n, (k + i) :=
    Nat.ascFactorial_eq_prod_range k n
  have hp_dvd_prod : p ∣ ∏ i ∈ Finset.range n, (k + i) := by
    rw [← hprod_eq_range, hprod_eq]
    exact dvd_mul_of_dvd_right hp_dvd (n !)
  rw [hp.prime.dvd_finsetProd_iff] at hp_dvd_prod
  simpa [Finset.mem_range] using hp_dvd_prod

end Nat.SylvesterSchur

namespace Nat.SylvesterSchur

/--
[consecutive_of_exists_prime_dvd_choose](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/Bridge.lean)
-/
@[path]
lemma consecutive_of_exists_prime_dvd_choose
  {n k : ℕ}
-- given
  (hbin : ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n) :
-- imply
  ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i := by
-- proof
  obtain ⟨p, hp, hp_gt, hp_dvd⟩ := hbin
  obtain ⟨i, hi, hi_dvd⟩ :=
    exists_dvd_consecutive_of_prime_dvd_choose n k p hp hp_dvd
  exact ⟨i, hi, p, hp, hp_gt, hi_dvd⟩

end Nat.SylvesterSchur


-- created on 2026-10-20
-- updated on 2026-10-26
