import sympy.sets.sets
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Set.Ico.ne.Empty.is.Gt |
| mpr | Set.Ico.ne.Empty.of.Gt |
-/
@[main, mpr]
private lemma main
  {a b : ℤ} :
-- imply
  Finset.Ico a b ≠ ∅ ↔ a < b :=
-- proof
  ⟨fun h => Finset.nonempty_Ico.mp (Finset.nonempty_iff_ne_empty.mpr h), fun h => (Finset.nonempty_Ico.mpr h).ne_empty⟩


-- created on 2026-10-07
