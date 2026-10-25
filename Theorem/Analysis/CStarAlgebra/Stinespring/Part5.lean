/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Def.Analysis.CStarAlgebra.Stinespring.Part6


section

open scoped CStarAlgebra InnerProduct

open scoped ComplexOrder InnerProductSpace

universe u

namespace MetaMathlibExt.Stinespring

theorem stinespringLeftMul_apply (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (c : A) (f : StinespringPre A H φ) :
    (stinespringLeftMul A H φ c) f = stinespringLeftMul0 A H φ c f := rfl

-- N9 add
theorem stinespringRep_add (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (c d : A) :
    stinespringRep A H φ (c + d) = stinespringRep A H φ c + stinespringRep A H φ d := by
  apply ContinuousLinearMap.ext
  intro z
  induction z using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih g =>
    simp only [stinespringRep, ContinuousLinearMap.completion_apply_coe, add_apply,
      ← UniformSpace.Completion.coe_add, stinespringLeftMul_apply]
    apply completion_coe_eq_of_inner_eq
    intro w
    rw [stinespringLeftMul0_inner, stinespringPhi_add, ← stinespringLeftMul0_inner,
      ← stinespringLeftMul0_inner, ← inner_add_right]

-- N9 smul
theorem stinespringRep_smul (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (r : ℂ) (c : A) :
    stinespringRep A H φ (r • c) = r • stinespringRep A H φ c := by
  apply ContinuousLinearMap.ext
  intro z
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (stinespringRep A H φ (r • c)).continuous
      (ContinuousLinearMap.continuous _)
  | ih g =>
    simp only [stinespringRep, ContinuousLinearMap.completion_apply_coe, smul_apply,
      ← UniformSpace.Completion.coe_smul, stinespringLeftMul_apply]
    apply completion_coe_eq_of_inner_eq
    intro w
    rw [stinespringLeftMul0_inner, stinespringPhi_smul, ← stinespringLeftMul0_inner,
      ← inner_smul_right]

theorem stinespringRep_zero (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) : stinespringRep A H φ 0 = 0 := by
  have h := stinespringRep_smul A H φ (0 : ℂ) (0 : A)
  simp only [smul_zero, zero_smul] at h
  exact h

-- N10 mul
theorem stinespringRep_mul (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (c d : A) :
    stinespringRep A H φ (c * d) = stinespringRep A H φ c * stinespringRep A H φ d := by
  apply ContinuousLinearMap.ext
  intro z
  induction z using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih g =>
    simp only [stinespringRep, ContinuousLinearMap.completion_apply_coe, mul_apply_eq_comp,
      stinespringLeftMul_apply]
    rw [stinespringLeftMul0_mul]
    rfl

-- N10 one
theorem stinespringRep_one (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) : stinespringRep A H φ 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro z
  induction z using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih g =>
    simp only [stinespringRep, ContinuousLinearMap.completion_apply_coe,
      stinespringLeftMul_apply, stinespringLeftMul0_one, LinearMap.id_apply,
      one_apply_eq_self]

-- N10 star
theorem stinespringRep_star (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (c : A) :
    stinespringRep A H φ (star c) = star (stinespringRep A H φ c) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).mpr ?_
  intro x y
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    simp only [stinespringRep, ContinuousLinearMap.completion_apply_coe,
      stinespringLeftMul_apply, UniformSpace.Completion.inner_coe]
    rw [stinespringLeftMul0_adj, star_star]

end MetaMathlibExt.Stinespring
end
