import sympy.functions.elementary.complexes
import sympy.Basic
import Lemma.Complex.Square.Abs.eq.Add.Re


@[main]
private lemma main
  {n : ℕ}
  {a : ℕ → ℂ} :
-- imply
  ∑ i ∈ Finset.range n, ‖a i‖ ^ 2 = ‖∑ i ∈ Finset.range n, a i‖ ^ 2 - ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, 2 * (~(a i) * a j).re := by
-- proof
  rw [Complex.Square.Abs.eq.Add.Re]
  ring


-- created on 2023-06-24
