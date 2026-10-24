import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Complex.Wiman.InfiniteTaylorSupport
open Complex


namespace Complex

/--
[infinite_support_wimanTaylorCoefficient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/InfiniteTaylorSupport.lean)
-/
@[path]
lemma infinite_support_wimanTaylorCoefficient
  {f : ℂ → ℂ}
-- given
  (hf : Differentiable ℂ f)
  (htrans : IsTranscendental f) :
-- imply
  (Function.support (wimanTaylorCoefficient f)).Infinite := by
-- proof
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



-- created on 2026-10-20
-- updated on 2026-10-23
