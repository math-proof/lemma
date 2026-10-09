import sympy.concrete.continued_fraction
import sympy.Basic
open Continuant


@[path]
private lemma main :
-- imply
  ∀ {l : List ℝ}, l ≠ [] → (∀ a ∈ l, 0 < a) → 0 < alpha l := by
-- proof
  intro p₀ p₁ p₂
  match p₀, p₁, p₂ with
  | [], hl, _ => exact absurd rfl hl
  | [a], _, h =>
    simpa [alpha] using h a (by simp)
  | a :: b :: l, _, h =>
    have ih := main (l := b :: l) (by simp) (fun c hc => h c (List.mem_cons_of_mem a hc))
    have ha := h a (by simp)
    exact add_pos ha (one_div_pos.mpr ih)


-- created on 2026-10-07
