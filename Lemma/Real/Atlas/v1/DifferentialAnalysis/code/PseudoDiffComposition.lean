import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.PseudoDiffComposition
open Filter Topology MeasureTheory PoissonEquation PoissonEquation.SmoothZeroAtInfty
open scoped SchwartzMap


namespace PoissonEquation.SmoothZeroAtInfty

/--
[ext](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PseudoDiffComposition.lean)
-/
@[path]
lemma ext
  {n : ℕ}
  {n}
  {f g : SmoothZeroAtInfty n}
-- given
  (h : ∀ x, f x = g x) :
-- imply
  f = g :=
-- proof
  DFunLike.coe_injective (funext h)

end PoissonEquation.SmoothZeroAtInfty

namespace PoissonEquation.SmoothZeroAtInfty

/--
[smooth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PseudoDiffComposition.lean)
-/
@[path]
lemma smooth
  {n : ℕ}
  {n}
  {f : SmoothZeroAtInfty n} :
-- imply
  ContDiff ℝ (⊤ : ℕ∞) (⇑f) :=
-- proof
  f.smooth'

end PoissonEquation.SmoothZeroAtInfty

namespace PoissonEquation.SmoothZeroAtInfty

/--
[zero_at_infty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PseudoDiffComposition.lean)
-/
@[path]
lemma zero_at_infty
  {n : ℕ}
  {n}
  {f : SmoothZeroAtInfty n}
  {m : ℕ} :
-- imply
  Tendsto (fun x => ‖iteratedFDeriv ℝ m (⇑f) x‖) (cocompact _) (𝓝 0) :=
-- proof
  f.zero_at_infty' m

end PoissonEquation.SmoothZeroAtInfty


-- created on 2026-10-23
