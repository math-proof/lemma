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
public import Instance.Analysis.CStarAlgebra.Stinespring

@[expose] public section

section

open scoped CStarAlgebra InnerProduct

open scoped ComplexOrder InnerProductSpace

universe u

namespace MetaMathlibExt.Stinespring

noncomputable def StinespringPre.toPre (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) : (A →₀ H) ≃ₗ[ℂ] StinespringPre A H φ :=
  LinearEquiv.refl ℂ _

noncomputable def StinespringPre.ofPre (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) : StinespringPre A H φ ≃ₗ[ℂ] (A →₀ H) :=
  (StinespringPre.toPre A H φ).symm

end MetaMathlibExt.Stinespring
end
