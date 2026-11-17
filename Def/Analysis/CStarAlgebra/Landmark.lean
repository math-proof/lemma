/-
  Author: @toskua, Avocado
-/

module

public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Lp.lpHolder
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Tactic.Positivity
public import Abbrev.Analysis.CStarAlgebra.Landmark

@[expose] public section

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
