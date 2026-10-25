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
import Abbrev.Analysis.CStarAlgebra.Stinespring


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
