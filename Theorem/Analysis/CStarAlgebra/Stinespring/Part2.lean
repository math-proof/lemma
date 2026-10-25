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
import Def.Analysis.CStarAlgebra.Stinespring


section

open scoped CStarAlgebra InnerProduct

open scoped ComplexOrder InnerProductSpace

universe u

namespace MetaMathlibExt.Stinespring

-- N4 (i)
theorem stinespringForm_add_left {A H : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (f f' g : A →₀ H) :
    stinespringForm φ (f + f') g = stinespringForm φ f g + stinespringForm φ f' g := by
  simp only [stinespringForm]
  rw [Finsupp.sum_add_index']
  · intro a
    simp
  · intro a x₁ x₂
    simp only [inner_add_left, Finsupp.sum_add]

-- N4 (ii)
theorem stinespringForm_smul_left {A H : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (r : ℂ) (f g : A →₀ H) :
    stinespringForm φ (r • f) g = (starRingEnd ℂ) r * stinespringForm φ f g := by
  simp only [stinespringForm]
  rw [Finsupp.sum_smul_index']
  · simp only [inner_smul_left, Finsupp.mul_sum]
  · intro a
    simp

-- N4 (iii)
theorem stinespringForm_conj_symm {A H : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (f g : A →₀ H) :
    (starRingEnd ℂ) (stinespringForm φ g f) = stinespringForm φ f g := by
  have hop : ∀ a b : A, φ (star a * b)
      = ContinuousLinearMap.adjoint (φ (star b * a)) := by
    intro a b
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star φ, star_mul, star_star]
  have term : ∀ (a : A) (x : H) (b : A) (y : H),
      (starRingEnd ℂ) ⟪x, φ (star a * b) y⟫_ℂ = ⟪y, φ (star b * a) x⟫_ℂ := by
    intro a x b y
    rw [inner_conj_symm, hop a b, ContinuousLinearMap.adjoint_inner_left]
  simp only [stinespringForm, map_finsuppSum, term]
  exact (Finsupp.sum_comm f g _).symm

-- N4 (iv)
theorem stinespringForm_single {A H : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (a b : A) (x y : H) :
    stinespringForm φ (Finsupp.single a x) (Finsupp.single b y)
      = ⟪x, φ (star a * b) y⟫_ℂ := by
  simp only [stinespringForm]
  rw [Finsupp.sum_single_index (by simp)]
  rw [Finsupp.sum_single_index (by simp [map_zero])]

-- N4 (v)
theorem stinespringForm_self {A H : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (f : A →₀ H) :
    stinespringForm φ f f
      = ∑ a ∈ f.support, ∑ b ∈ f.support, ⟪f a, φ (star a * b) (f b)⟫_ℂ := rfl

end MetaMathlibExt.Stinespring
end
