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
public import Theorem.Analysis.CStarAlgebra.Stinespring.Part4

@[expose] public section

section

open scoped CStarAlgebra InnerProduct

open scoped ComplexOrder InnerProductSpace

universe u

namespace MetaMathlibExt.Stinespring

-- N7b bounded version
noncomputable def stinespringLeftMul (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (c : A) : StinespringPre A H φ →L[ℂ] StinespringPre A H φ :=
  (stinespringLeftMul0 A H φ c).mkContinuous ‖c‖ (stinespringLeftMul0_bound A H φ c)

end MetaMathlibExt.Stinespring
end
