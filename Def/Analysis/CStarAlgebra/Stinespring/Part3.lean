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
import Instance.Analysis.CStarAlgebra.Stinespring


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
