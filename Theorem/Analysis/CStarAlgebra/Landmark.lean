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
import Def.Analysis.CStarAlgebra.Landmark


section

open scoped InnerProductSpace ComplexOrder

universe u

namespace Analysis.CStarAlgebra.LandmarkWanted

/-- Componentwise action of `repOp`. -/
theorem repOp_apply (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (a : A) (x : UH A) (f : A →ₚ[ℂ] ℂ) :
    (repOp A a x) f = f.gnsStarAlgHom a (x f) := rfl

/-- Two operators on `UH A` agree if all their components agree. -/
theorem repOp_ext (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (X Y : (UH A) →L[ℂ] (UH A))
    (h : ∀ (x : UH A) (f : A →ₚ[ℂ] ℂ), (X x) f = (Y x) f) : X = Y :=
  ContinuousLinearMap.ext fun x => lp.ext (funext fun f => h x f)

end Analysis.CStarAlgebra.LandmarkWanted
end
