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
public import Def.Analysis.CStarAlgebra.Stinespring.Part2
@[expose] public section

section

open scoped CStarAlgebra InnerProduct

open scoped ComplexOrder InnerProductSpace

universe u

namespace MetaMathlibExt.Stinespring

noncomputable instance StinespringPre_addCommGroup (A H : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (φ : A →CP (H →L[ℂ] H)) : AddCommGroup (StinespringPre A H φ) :=
  inferInstanceAs (AddCommGroup (A →₀ H))

noncomputable instance StinespringPre_module (A H : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (φ : A →CP (H →L[ℂ] H)) : Module ℂ (StinespringPre A H φ) :=
  inferInstanceAs (Module ℂ (A →₀ H))

end MetaMathlibExt.Stinespring
end
