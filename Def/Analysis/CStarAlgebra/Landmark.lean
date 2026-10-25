/-
  Author: @toskua, Avocado
-/
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Tactic.Positivity
import Abbrev.Analysis.CStarAlgebra.Landmark


section

open scoped InnerProductSpace ComplexOrder

universe u

namespace Analysis.CStarAlgebra.LandmarkWanted

/-- The operator of the universal representation at `a`: acts as `f.gnsStarAlgHom a` in each
component `f`. Uniformly bounded by `‖a‖`. -/
noncomputable def repOp (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (a : A) : (UH A) →L[ℂ] (UH A) :=
  lp.mapCLM 2 (fun f => f.gnsStarAlgHom a) (K := ‖a‖) (by positivity)
    (fun f => NonUnitalStarAlgHom.norm_apply_le (f.gnsStarAlgHom) a)

end Analysis.CStarAlgebra.LandmarkWanted
end
