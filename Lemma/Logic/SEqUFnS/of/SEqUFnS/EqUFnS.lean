import stdlib.SEq
import sympy.Basic


@[main]
private lemma mpr
  {Vector : α → Sort v}
  {f f' : ι → β}
  {p : β → Vector n}
  {g : ι → Vector m}
-- given
  (h₀ : f i = f' i)
  (h₁ : p (f' i) ≃ g i) :
-- imply
  p (f i) ≃ g i := by
-- proof
  simp [SEq] at *
  simp_all


@[main]
private lemma main
  {Vector : α → Sort v}
  {f f' : ι → β}
  {p : β → Vector n}
  {g : ι → Vector m}
-- given
  (h₀ : f i = f' i)
  (h₁ : p (f i) ≃ g i) :
-- imply
  p (f' i) ≃ g i := by
-- proof
  simp [SEq] at *
  simp_all


-- created on 2025-05-23
