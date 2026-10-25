/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/SocialistPrime.lean -/


import Def.NumberTheory.SocialistPrime
import Lemma.Nat.SocialistPrime


-- 5 is excluded by the strict source bound 5 < p; its listed residues
-- in [2,4] happen to be distinct.
example : ¬ Nat.IsSocialistPrime 5 := by
  intro h
  have h5 := h.five_lt
  omega

-- 3! = 6, 6! = 720; both ≡ 6 mod 7, witnessing the collision cited in required_tests.
example : (3 : ℕ).factorial % 7 = 6 := by decide

example : (6 : ℕ).factorial % 7 = 6 := by decide

example : (3 : ℕ).factorial % 7 = (6 : ℕ).factorial % 7 := by decide

-- 7 is prime and >5 but fails pairwise distinctness via 3! ≡ 6! [MOD 7].
example : ¬ Nat.IsSocialistPrime 7 := by
  intro h
  have hp := h.pairwise
  have ha : (3 : ℕ) ∈ Set.Icc 2 (7 - 1) := by simp
  have hb : (6 : ℕ) ∈ Set.Icc 2 (7 - 1) := by simp
  have hne : (3 : ℕ) ≠ 6 := by omega
  have hdistinct := hp ha hb hne
  have heq : (3 : ℕ).factorial % 7 = (6 : ℕ).factorial % 7 := by decide
  exact hdistinct heq

-- Exercise generic pairwise API for arbitrary p, a, b via the elimination lemma.
example {p a b : ℕ} (h : Nat.IsSocialistPrime p)
    (ha : a ∈ Set.Icc 2 (p - 1)) (hb : b ∈ Set.Icc 2 (p - 1)) (hab : a ≠ b) :
    a.factorial % p ≠ b.factorial % p :=
  h.factorial_mod_ne ha hb hab

