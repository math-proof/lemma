import Mathlib
import sympy.Basic


namespace MetaMathlibExt

/--
[binomial_harmonic_interchange_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BinomialHarmonicInterchangeIdentity.lean)
-/
@[path]
lemma binomial_harmonic_interchange_identity
  [Field K] [CharZero K]
  {n : ℕ}
  {a : ℕ → K} :
-- imply
  Finset.sum (Finset.Icc 1 n)
    (fun k => (1 / (k : K)) *
    Finset.sum (Finset.Icc 1 k) (fun j => (Nat.choose k j : K) * a j)) =
    Finset.sum (Finset.Icc 1 n) (fun k => (Nat.choose n k : K) * a k / (k : K)) := by
-- proof
  induction n with
  | zero => simp
  | succ n ih =>
    have hle : (1 : ℕ) ≤ n + 1 := by omega
    have hN : ((n + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
    have absorb : ∀ k ∈ Finset.Icc 1 n,
      (1 / ((n + 1 : ℕ) : K)) * ((Nat.choose (n + 1) k : K) * a k) =
        (Nat.choose n (k - 1) : K) * a k / (k : K) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hkk : (k - 1) + 1 = k := by omega
      have hnat := Nat.add_one_mul_choose_eq n (k - 1)
      rw [hkk] at hnat
      have hkK : (k : K) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      have hcast : ((n + 1 : ℕ) : K) * (Nat.choose n (k - 1) : K) =
        (Nat.choose (n + 1) k : K) * (k : K) := by
        exact_mod_cast hnat
      have e1 : (1 / ((n + 1 : ℕ) : K)) * ((Nat.choose (n + 1) k : K) * a k)
        = ((Nat.choose (n + 1) k : K) * a k) / ((n + 1 : ℕ) : K) := by ring
      rw [e1, div_eq_div_iff hN hkK]
      linear_combination -(a k) * hcast
    have pascal : ∀ k ∈ Finset.Icc 1 n,
      (Nat.choose (n + 1) k : K) * a k / (k : K) =
        (Nat.choose n k : K) * a k / (k : K) +
          (Nat.choose n (k - 1) : K) * a k / (k : K) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hnat : Nat.choose (n + 1) k =
        Nat.choose n (k - 1) + Nat.choose n k := by
        have hps := Nat.choose_succ_succ n (k - 1)
        rwa [show (k - 1).succ = k from by omega,
          show n.succ = n + 1 from rfl] at hps
      have hcast : (Nat.choose (n + 1) k : K) =
        (Nat.choose n (k - 1) : K) + (Nat.choose n k : K) := by
        exact_mod_cast hnat
      rw [hcast]
      ring
    have hA : (1 / ((n + 1 : ℕ) : K)) *
      Finset.sum (Finset.Icc 1 (n + 1))
        (fun j => (Nat.choose (n + 1) j : K) * a j) =
      Finset.sum (Finset.Icc 1 n)
        (fun k => (Nat.choose n (k - 1) : K) * a k / (k : K)) +
      (Nat.choose (n + 1) (n + 1) : K) * a (n + 1) / ((n + 1 : ℕ) : K) := by
      rw [Finset.sum_Icc_succ_top hle, mul_add, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl (fun k hk => absorb k hk)
      · ring
    have hB : Finset.sum (Finset.Icc 1 n)
      (fun k => (Nat.choose (n + 1) k : K) * a k / (k : K)) =
      Finset.sum (Finset.Icc 1 n)
        (fun k => (Nat.choose n k : K) * a k / (k : K)) +
      Finset.sum (Finset.Icc 1 n)
        (fun k => (Nat.choose n (k - 1) : K) * a k / (k : K)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k hk => pascal k hk)
    conv_lhs => rw [Finset.sum_Icc_succ_top hle]
    conv_rhs => rw [Finset.sum_Icc_succ_top hle]
    rw [ih]
    linear_combination hA - hB

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
