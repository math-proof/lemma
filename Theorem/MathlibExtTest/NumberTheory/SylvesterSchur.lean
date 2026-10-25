/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/SylvesterSchur.lean -/


import Lemma.Nat.SylvesterSchur


example {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ n.ascFactorial k :=
  Nat.exists_prime_gt_and_dvd_ascFactorial hk hkn

