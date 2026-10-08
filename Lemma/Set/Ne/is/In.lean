import Lemma.Set.Ne.of.In
import Lemma.Set.NotIn.of.Ne
import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x y : Fin n → ℂ} :
-- imply
  x ≠ y ↔ x ∈ Set.univ \ {y} := by
-- proof
  constructor
  · intro h
    exact ⟨Set.mem_univ x, Set.NotIn.of.Ne h⟩
  · intro h
    apply Set.Ne.of.In h


-- created on 2021-08-16
