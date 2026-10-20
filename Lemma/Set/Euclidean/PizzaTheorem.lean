import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.PizzaTheorem
open scoped BigOperators
open MetaMathlibExt


/--
[pizza_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/PizzaTheorem.lean)
-/
@[path]
private lemma pizza_theorem_eq
  {n : ℕ}
  {c p : ℝ × ℝ}
  {R θ₀ : ℝ}
-- given
  (hn : 2 ≤ n)
  (hR : 0 < R)
  (hp : p ∈ {x : ℝ × ℝ | (x.1 - c.1) ^ 2 + (x.2 - c.2) ^ 2 < R ^ 2}) :
-- imply
  ∑ k ∈ Finset.filter (fun k => k % 2 = 0) (Finset.range (4 * n)),
    MeasureTheory.volume ({x : ℝ × ℝ | (x.1 - c.1) ^ 2 + (x.2 - c.2) ^ 2 < R ^ 2} ∩
    {x | ∃ r θ : ℝ, 0 ≤ r ∧
    θ₀ + (k : ℝ) * (Real.pi / (2 * (n : ℝ))) ≤ θ ∧
    θ < θ₀ + ((k : ℝ) + 1) * (Real.pi / (2 * (n : ℝ))) ∧
    x = p + r • (Real.cos θ, Real.sin θ)}) =
    ∑ k ∈ Finset.filter (fun k => k % 2 = 1) (Finset.range (4 * n)),
    MeasureTheory.volume ({x : ℝ × ℝ | (x.1 - c.1) ^ 2 + (x.2 - c.2) ^ 2 < R ^ 2} ∩
    {x | ∃ r θ : ℝ, 0 ≤ r ∧
    θ₀ + (k : ℝ) * (Real.pi / (2 * (n : ℝ))) ≤ θ ∧
    θ < θ₀ + ((k : ℝ) + 1) * (Real.pi / (2 * (n : ℝ))) ∧
    x = p + r • (Real.cos θ, Real.sin θ)}) := by
-- proof
  apply MetaMathlibExt.pizza_theorem n hn c p R hR hp θ₀


-- created on 2026-10-20
