/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/RadialMajorant.lean -/

import Theorem.Analysis.Complex.Wiman.TaylorExpansion
import Lemma.Complex.Wiman.TaylorExpansion


namespace Complex

noncomputable section

/-- The positive radial majorant formed from the norms of the Taylor coefficients at radius
`|r|`. -/
def wimanMajorant (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  ∑' n, wimanTerm f r n

end
end Complex
