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
import Theorem.Analysis.CStarAlgebra.Landmark


section

open scoped InnerProductSpace ComplexOrder

universe u

namespace Analysis.CStarAlgebra.LandmarkWanted

/-- The universal GNS representation as a star-algebra homomorphism. -/
noncomputable def repHom (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] : A →⋆ₐ[ℂ] ((UH A) →L[ℂ] (UH A)) where
  toFun a := repOp A a
  map_one' := by
    apply repOp_ext A
    intro x f
    simp only [repOp_apply, map_one, one_apply_eq_self]
  map_mul' := by
    intro a b
    apply repOp_ext A
    intro x f
    simp [repOp_apply]
  map_zero' := by
    apply repOp_ext A
    intro x f
    simp [repOp_apply]
  map_add' := by
    intro a b
    apply repOp_ext A
    intro x f
    simp [repOp_apply]
  commutes' := by
    intro r
    apply repOp_ext A
    intro x f
    rw [repOp_apply, AlgHomClass.commutes (f.gnsStarAlgHom) r]
    simp [Algebra.algebraMap_eq_smul_one]
  map_star' := by
    intro a
    show repOp A (star a) = star (repOp A a)
    rw [ContinuousLinearMap.star_eq_adjoint]
    refine (ContinuousLinearMap.eq_adjoint_iff _ _).mpr ?_
    intro x y
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    refine tsum_congr fun f => ?_
    rw [repOp_apply, repOp_apply]
    have hcomp : f.gnsStarAlgHom (star a)
        = ContinuousLinearMap.adjoint (f.gnsStarAlgHom a) := by
      rw [← ContinuousLinearMap.star_eq_adjoint]
      exact map_star _ _
    rw [hcomp]
    exact ContinuousLinearMap.adjoint_inner_left _ _ _

end Analysis.CStarAlgebra.LandmarkWanted
end
