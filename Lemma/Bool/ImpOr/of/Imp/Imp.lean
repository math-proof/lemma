import sympy.Basic


@[main]
private lemma main
  {p q r : Prop}
-- given
  (h₀ : p → r)
  (h₁ : q → r) :
-- imply
  p ∨ q → r := by
-- proof
    -- Introduce the hypothesis `h : p ∨ q`
  intro h
    -- Split `h` into two cases: `hp : p` and `hq : q`
  cases h with
  | inl hp =>
      -- Case 1: `hp : p`
      -- Apply `h₀ : p → r` to `hp` to get `r`
    apply h₀
    assumption
  | inr hq =>
      -- Case 2: `hq : q`
      -- Apply `h₁ : q → r` to `hq` to get `r`
    apply h₁
    assumption


-- created on 2025-04-18
