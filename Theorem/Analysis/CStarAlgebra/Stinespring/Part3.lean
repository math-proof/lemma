/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Instance.Analysis.CStarAlgebra.Stinespring.Part2

public section

section

open scoped CStarAlgebra InnerProduct

open scoped ComplexOrder InnerProductSpace

universe u

namespace MetaMathlibExt.Stinespring

theorem stinespring_pre_inner_def (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (f g : StinespringPre A H φ) :
    ⟪f, g⟫_ℂ = stinespringForm φ (StinespringPre.ofPre A H φ f)
      (StinespringPre.ofPre A H φ g) := rfl

theorem stinespring_pre_inner_single (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (a b : A) (x y : H) :
    ⟪StinespringPre.toPre A H φ (Finsupp.single a x),
      StinespringPre.toPre A H φ (Finsupp.single b y)⟫_ℂ
      = ⟪x, φ (star a * b) y⟫_ℂ := by
  rw [stinespring_pre_inner_def]
  exact stinespringForm_single φ a b x y

-- N6 auxiliary simp lemmas
@[simp] theorem StinespringPre.toPre_ofPre (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (a : StinespringPre A H φ) :
    StinespringPre.toPre A H φ (StinespringPre.ofPre A H φ a) = a := rfl

@[simp] theorem StinespringPre.ofPre_toPre (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (a : A →₀ H) :
    StinespringPre.ofPre A H φ (StinespringPre.toPre A H φ a) = a := rfl

end MetaMathlibExt.Stinespring
end
