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
public import Theorem.Analysis.CStarAlgebra.Stinespring.Part6


public section

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
section

open scoped CStarAlgebra InnerProduct

open scoped ComplexOrder InnerProductSpace

universe u

namespace MetaMathlibExt.Stinespring

-- N12 V0 and bound
noncomputable def stinespringV0 (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) : H →ₗ[ℂ] StinespringPre A H φ :=
  (StinespringPre.toPre A H φ).toLinearMap ∘ₗ Finsupp.lsingle 1

end MetaMathlibExt.Stinespring
end
