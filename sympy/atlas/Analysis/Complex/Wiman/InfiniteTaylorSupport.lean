/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/InfiniteTaylorSupport.lean -/

import sympy.atlas.Analysis.Complex.Wiman.TaylorExpansion
namespace Complex

noncomputable section

/-- A transcendental entire function has infinitely many nonzero Taylor coefficients. -/
theorem infinite_support_wimanTaylorCoefficient
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (htrans : IsTranscendental f) :
    (Function.support (wimanTaylorCoefficient f)).Infinite := by
  intro hfinite
  apply htrans
  let s : Finset ℕ := hfinite.toFinset
  let p : Polynomial ℂ :=
    ∑ n ∈ s, Polynomial.monomial n (wimanTaylorCoefficient f n)
  refine ⟨p, fun z ↦ ?_⟩
  have hzero : ∀ n ∉ s, wimanTaylorCoefficient f n * z ^ n = 0 := by
    intro n hn
    have hcoeff : wimanTaylorCoefficient f n = 0 := by
      simpa [s, Function.mem_support] using hn
    simp [hcoeff]
  rw [← (hasSum_wimanTaylorCoefficient_mul_pow f hf z).tsum_eq,
    tsum_eq_sum hzero]
  simp [p, Polynomial.eval_finsetSum]

end
