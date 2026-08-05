import sympy.Basic
import sympy.concrete.quantifier


/--
| attributes | lemma |
| :---: | :---: |
| main | Fin.All_UFn.is.AndAll |
| comm | Fin.AndAll.is.All_UFn |
| mp | Fin.AndAll.of.All_UFn |
| mpr | Fin.All_UFn.of.AndAll |
-/
@[main, comm, mp, mpr]
private lemma main
  {n : ℕ}
  {p : Fin (n + 1) → Prop} :
-- imply
  (∀ i : Fin (n + 1), p i) ↔ (∀ i : Fin n, p (Fin.castSucc i)) ∧ p (Fin.last n) := by
-- proof
  constructor
  · intro h
    constructor
    · intro i
      exact h (Fin.castSucc i)
    · exact h (Fin.last n)
  · intro ⟨h₀, h₁⟩ i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | ⟨rfl⟩
    · exact h₀ i
    · exact h₁


-- created on 2018-04-24
