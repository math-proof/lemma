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
import Def.Analysis.CStarAlgebra.Stinespring.Part9


section

open scoped CStarAlgebra InnerProduct

open scoped ComplexOrder InnerProductSpace

universe u

namespace MetaMathlibExt.Stinespring

theorem stinespringV_apply (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (x : H) :
    stinespringV A H φ x
      = ((StinespringPre.toPre A H φ (Finsupp.single 1 x) :
        StinespringPre A H φ) : stinespringK A H φ) := by
  simp only [stinespringV, ContinuousLinearMap.coe_comp, Function.comp_apply,
    LinearMap.mkContinuous_apply, stinespringV0_apply,
    UniformSpace.Completion.coe_toComplL]

-- N12 key identity
theorem stinespringV_inner_rep (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (a : A) (x y : H) :
    ⟪stinespringV A H φ y, stinespringStarAlgHom A H φ a (stinespringV A H φ x)⟫_ℂ
      = ⟪y, φ a x⟫_ℂ := by
  simp only [stinespringV_apply, stinespringStarAlgHom_apply, stinespringRep,
    ContinuousLinearMap.completion_apply_coe, stinespringLeftMul_apply,
    stinespringLeftMul0, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    StinespringPre.ofPre_toPre, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    UniformSpace.Completion.inner_coe, stinespring_pre_inner_def,
    stinespringForm_single]
  rw [star_one, one_mul, mul_one]

end MetaMathlibExt.Stinespring

namespace Analysis.CStarAlgebra.StinespringWanted

/--
Every completely positive map `φ : A →CP B(H)` from a unital C*-algebra `A` to `B(H)` dilates as
`φ a = V† (π a) V` for some Hilbert space `K`, `∗`-homomorphism `π : A →⋆ₐ B(K)` and `V : H →L[ℂ]
K`. Source: Stinespring dilation theorem, W. F. Stinespring, Proc. Amer. Math. Soc. 6 (1955); see
Paulsen, Completely Bounded Maps; Lean is general CP map A →CP B(H) dilation V† π(a) V, not
finite-dimensional Kraus form.

Proves `Wanted` entry `stinespring_dilation`.
-/
theorem stinespring_dilation
    {A H : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K)
        (_ : CompleteSpace K) (π : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K),
      ∀ (a : A) (x : H), (φ a) x = (V†) ((π a) (V x)) := by
  refine ⟨MetaMathlibExt.Stinespring.stinespringK A H φ, inferInstance, inferInstance,
    inferInstance, MetaMathlibExt.Stinespring.stinespringStarAlgHom A H φ,
    MetaMathlibExt.Stinespring.stinespringV A H φ, ?_⟩
  intro a x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (MetaMathlibExt.Stinespring.stinespringV_inner_rep A H φ a x y).symm

end Analysis.CStarAlgebra.StinespringWanted
end
