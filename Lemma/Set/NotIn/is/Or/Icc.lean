import sympy.sets.sets
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Set.NotIn.is.Or.Icc |
| mp | Set.Or.Icc.of.NotIn |
| mpr | Set.NotIn.of.Or.Icc |
-/
@[main, mp, mpr]
private lemma main
  {x a b : ℝ} :
-- imply
  x ∉ Set.Ico a b ↔ x = b ∨ x ∉ Set.Icc a b := by
-- proof
  constructor
  ·
    intro h
    if hxb : x = b then
      exact Or.inl hxb
    else
      apply Or.inr
      intro hmem
      exact h ⟨hmem.1, lt_of_le_of_ne hmem.2 hxb⟩
  ·
    intro h
    obtain h | h := h
    ·
      rw [h]
      simp
    ·
      intro hx
      exact h ⟨hx.1, hx.2.le⟩


-- created on 2026-10-07
