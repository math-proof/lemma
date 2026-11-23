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
public import Theorem.Analysis.CStarAlgebra.Stinespring.Part3

@[expose] public section

section

open scoped CStarAlgebra InnerProduct

open scoped ComplexOrder InnerProductSpace

universe u

namespace MetaMathlibExt.Stinespring

-- N6 definition
noncomputable def stinespringLeftMul0 (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (c : A) : StinespringPre A H φ →ₗ[ℂ] StinespringPre A H φ :=
  (StinespringPre.toPre A H φ).toLinearMap ∘ₗ
    Finsupp.lmapDomain H ℂ (fun a => c * a) ∘ₗ
      (StinespringPre.ofPre A H φ).toLinearMap

-- N6 Phi definition (right side of inner formula)
noncomputable def stinespringPhi (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (f : StinespringPre A H φ) (c : A)
    (g : StinespringPre A H φ) : ℂ :=
  (StinespringPre.ofPre A H φ f).sum (fun a x =>
    (StinespringPre.ofPre A H φ g).sum (fun b y => ⟪x, φ (star a * (c * b)) y⟫_ℂ))

end MetaMathlibExt.Stinespring
end
