import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.FourierAnalysis.code.FourierOrthonormalBasis
open MeasureTheory MeasureTheory.Measure AddCircle FourierOrthonormalBasis


/--
[fourier_hilbertBasis](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/FourierOrthonormalBasis.lean)
-/
@[path]
private lemma main
  {T : ℝ} [hT : Fact (0 < T)] :
-- imply
  ∃ b : HilbertBasis ℤ ℂ (Lp ℂ 2 <| @haarAddCircle T hT), ⇑b = @fourierLp T hT 2 _ :=
-- proof
  ⟨fourierBasis, coe_fourierBasis⟩


-- created on 2026-10-23
-- updated on 2026-10-26
