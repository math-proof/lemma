import sympy.sets.sets
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Set.Ne_Empty.is.Any.split.Conditionset |
| mp | Set.Any.split.Conditionset.of.Ne_Empty |
| mpr | Set.Ne_Empty.of.Any.split.Conditionset |
-/
@[main, mp, mpr]
private lemma main
  {S : Set ℂ}
  {p : ℂ → Prop} :
-- imply
  {x | x ∈ S ∧ p x} ≠ ∅ ↔ ∃ x ∈ S, p x := by
-- proof
  constructor
  ·
    intro h
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr h
    exact ⟨x, hx.1, hx.2⟩
  ·
    intro ⟨x, hx, hp⟩
    exact Set.nonempty_iff_ne_empty.mp ⟨x, hx, hp⟩


-- created on 2026-10-07
