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
import Def.Analysis.CStarAlgebra.Stinespring.Part2


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
