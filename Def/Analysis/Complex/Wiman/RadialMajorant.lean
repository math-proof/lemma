/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/RadialMajorant.lean -/

module

public import Theorem.Analysis.Complex.Wiman.TaylorExpansion
public import Theorem.Complex.Wiman.TaylorExpansion

@[expose] public section

namespace Complex

noncomputable section

/-- The positive radial majorant formed from the norms of the Taylor coefficients at radius
`|r|`. -/
def wimanMajorant (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  ∑' n, wimanTerm f r n

end
end Complex
