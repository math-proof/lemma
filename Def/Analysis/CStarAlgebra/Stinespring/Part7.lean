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
public import Theorem.Analysis.CStarAlgebra.Stinespring.Part5


public section

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
section

open scoped CStarAlgebra InnerProduct

open scoped ComplexOrder InnerProductSpace

universe u

namespace MetaMathlibExt.Stinespring

-- N11 star algebra hom
noncomputable def stinespringStarAlgHom (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) : A →⋆ₐ[ℂ] (stinespringK A H φ →L[ℂ] stinespringK A H φ) where
  toFun := stinespringRep A H φ
  map_one' := stinespringRep_one A H φ
  map_mul' c d := stinespringRep_mul A H φ c d
  map_zero' := stinespringRep_zero A H φ
  map_add' c d := stinespringRep_add A H φ c d
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, stinespringRep_smul, stinespringRep_one]
  map_star' c := stinespringRep_star A H φ c

end MetaMathlibExt.Stinespring
end
