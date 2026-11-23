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
public import Abbrev.Analysis.CStarAlgebra.Stinespring
@[expose] public section

section

open scoped CStarAlgebra InnerProduct

open scoped ComplexOrder InnerProductSpace

universe u

namespace MetaMathlibExt.Stinespring

noncomputable instance StinespringPre_seminormed (A H : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (φ : A →CP (H →L[ℂ] H)) :
    SeminormedAddCommGroup (StinespringPre A H φ) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := stinespringCore A H φ)

noncomputable instance StinespringPre_inner (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) : InnerProductSpace ℂ (StinespringPre A H φ) :=
  InnerProductSpace.ofCore (stinespringCore A H φ)

end MetaMathlibExt.Stinespring
end
