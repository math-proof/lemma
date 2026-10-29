import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.Nat.SylvesterSchur.ErdosKey


namespace Nat

/--
[exists_prime_gt_and_dvd_ascFactorial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur.lean)
-/
@[path]
lemma exists_prime_gt_and_dvd_ascFactorial
  {n k : ℕ}
-- given
  (hk : 0 < k)
  (hkn : k < n) :
-- imply
  ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ n.ascFactorial k := by
-- proof
  obtain ⟨p, hp_prime, hp_gt, hp_dvd⟩ :=
    SylvesterSchur.Internal.erdos_choose_prime_factor_gt k hk n hkn
  obtain ⟨i, hi_lt, hi_dvd⟩ :=
    SylvesterSchur.exists_dvd_consecutive_of_prime_dvd_choose k n p hp_prime hp_dvd
  refine ⟨p, hp_prime, hp_gt, ?_⟩
  rw [Nat.ascFactorial_eq_prod_range]
  exact hi_dvd.trans (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hi_lt))

end Nat


-- created on 2026-10-20
-- updated on 2026-10-28
