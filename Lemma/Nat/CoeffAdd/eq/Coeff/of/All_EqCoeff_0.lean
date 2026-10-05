import Mathlib
import sympy.Basic


/--
[WittVector_add_coeff_eq_of_forall_coeff_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WittVector_add_coeff_eq_of_forall_coeff_eq_zero.lean)
-/
@[main]
private lemma main
  {S : Type u} [CommRing S]
  {p : ℕ} [Fact p.Prime]
  {x y : WittVector p S}
  {r : ℕ}
-- given
  (hx : ∀ i : ℕ, i < r → x.coeff i = 0) :
-- imply
  ∀ i : ℕ, i < r → (x + y).coeff i = y.coeff i := by
-- proof
  intro i hi
  have hker : WittVector.truncate r x = 0 := (WittVector.mem_ker_truncate r x).2 hx
  have h := congrArg (fun t : TruncatedWittVector p r S => t.coeff ⟨i, hi⟩) (map_add (WittVector.truncate r) x y)
  simp only [hker, zero_add, WittVector.coeff_truncate] at h
  exact h


-- created on 2026-10-05
