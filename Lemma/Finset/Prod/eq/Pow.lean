import Mathlib.Analysis.SpecialFunctions.Pow.Real
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {f : ℕ → ℝ}
  {a : ℝ}
-- given
  (h : ∀ i, f i ≥ 0) :
-- imply
  ∏ i ∈ Finset.range n, f i ^ a = (∏ i ∈ Finset.range n, f i) ^ a := by
-- proof
  exact Real.finsetProd_rpow _ _ (fun i _ => h i) a


-- created on 2023-03-30
