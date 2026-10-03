import Mathlib
import sympy.Basic


/--
[AddMonoidHom_exists_nsmul_eq_zero_and_apply_eq_of_surjective_of_forall_ker](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AddMonoidHom_exists_nsmul_eq_zero_and_apply_eq_of_surjective_of_forall_ker.lean)
-/
@[main]
private lemma main
  {A B : Type*} [AddCommGroup A] [AddCommGroup B]
  {f : A →+ B}
  {m : ℕ}
  {b : B}
-- given
  (hf : Function.Surjective f)
  (hdiv : ∀ k : A, f k = 0 → ∃ j : A, f j = 0 ∧ m • j = k)
  (hmb : m • b = 0) :
-- imply
  ∃ a : A, m • a = 0 ∧ f a = b := by
-- proof
  obtain ⟨a₀, ha₀⟩ := hf b
  have hker : f (m • a₀) = 0 := by rw [map_nsmul, ha₀, hmb]
  obtain ⟨j, hjker, hmj⟩ := hdiv (m • a₀) hker
  exact ⟨a₀ - j, by rw [smul_sub, hmj, sub_self], by rw [map_sub, ha₀, hjker, sub_zero]⟩


-- created on 2026-10-03
