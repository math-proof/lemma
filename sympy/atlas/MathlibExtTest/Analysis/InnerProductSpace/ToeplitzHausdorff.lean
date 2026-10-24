/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/InnerProductSpace/ToeplitzHausdorff.lean -/


import sympy.atlas.Analysis.InnerProductSpace.ToeplitzHausdorff

namespace MathlibExtTest.Analysis.InnerProductSpace.ToeplitzHausdorff

open MathlibExt.Analysis.InnerProductSpace.ToeplitzHausdorffWanted

example : (0 : ℂ) ∈ numericalRange (0 : ℂ →L[ℂ] ℂ) :=
  (mem_numericalRange_iff _ _).2 ⟨1, by simp, by simp⟩

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (A : E →L[ℂ] E) {x : E}
    (hx : ‖x‖ = 1) : inner (𝕜 := ℂ) (A x) x ∈ numericalRange A :=
  inner_mem_numericalRange A hx

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (A : E →L[ℂ] E) :
    Convex ℝ (numericalRange A) :=
  toeplitz_hausdorff_general A

end MathlibExtTest.Analysis.InnerProductSpace.ToeplitzHausdorff
