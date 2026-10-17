import Mathlib.Logic.Equiv.Defs
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {S : Set (Fin (n + 1) → α)}
-- given
  (h₀ : ∀ x ∈ S, ∀ j : Fin (n + 1), j ≠ 0 →
    (fun i => if i = j then x 0 else if i = 0 then x j else x i) ∈ S) :
-- imply
  ∀ x ∈ S, ∀ i j, (fun k => x (Equiv.swap i j k)) ∈ S := by
-- proof
  intro x hx i j
  have hstep : ∀ y ∈ S, ∀ t : Fin (n + 1), t ≠ 0 → (fun k => y (Equiv.swap 0 t k)) ∈ S := by
    intro y hy t ht
    have hy' := h₀ y hy t ht
    have heq : (fun k => y (Equiv.swap 0 t k)) =
        fun i => if i = t then y 0 else if i = 0 then y t else y i := by
      funext i
      if hit : i = t then
        subst hit
        simp [Equiv.swap_apply_right]
      else if hi0 : i = 0 then
        subst hi0
        simp [Equiv.swap_apply_left, hit]
      else
        rw [Equiv.swap_apply_of_ne_of_ne hi0 hit]
        simp [hit, hi0]
    simpa [heq] using hy'
  if hij : i = j then
    simpa [hij, Equiv.swap_self] using hx
  else if hi : i = 0 then
    subst hi
    simpa using hstep x hx j (by simpa using Ne.symm hij)
  else if hj : j = 0 then
    subst hj
    simpa [Equiv.swap_comm] using hstep x hx i hi
  else
    have hcomp : ∀ a, Equiv.swap 0 i (Equiv.swap 0 j (Equiv.swap 0 i a)) = Equiv.swap i j a := by
      intro a
      simp only [Equiv.swap_apply_def]
      split_ifs <;> simp_all
    have h1 := hstep x hx i hi
    have h2 := hstep _ h1 j hj
    have h3 := hstep _ h2 i hi
    simpa [hcomp] using h3


-- created on 2026-10-11
-- updated on 2026-10-17
