import sympy.Basic
import sympy.core.intfunc
import Mathlib.Algebra.GCDMonoid.Finset


@[main]
private lemma main
  {A : Set ℕ} [FiniteGCDOne A]
  {n : ℕ}
-- given
  (h : ∀ a ∈ A, n ∣ a) :
-- imply
  n = 1 := by
-- proof
  obtain ⟨s, hsA, hgcd1, _, _⟩ := (inferInstance : FiniteGCDOne A).finite_gcd_one
  have hn : n ∣ s.gcd id :=
    Finset.dvd_gcd fun b hb => h b (hsA hb)
  rw [hgcd1] at hn
  exact Nat.eq_one_of_dvd_one hn


-- created on 2026-09-22
