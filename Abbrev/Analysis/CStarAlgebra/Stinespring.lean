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
public import Def.Analysis.CStarAlgebra.Stinespring.Part3

@[expose] public section


section

open scoped CStarAlgebra InnerProduct

open scoped ComplexOrder InnerProductSpace

universe u

namespace MetaMathlibExt.Stinespring

noncomputable abbrev stinespringCore (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) : PreInnerProductSpace.Core ℂ (StinespringPre A H φ) where
  inner f g := stinespringForm φ (StinespringPre.ofPre A H φ f) (StinespringPre.ofPre A H φ g)
  conj_inner_symm f g := stinespringForm_conj_symm φ _ _
  re_inner_nonneg f := by
    show 0 ≤ RCLike.re (stinespringForm φ (StinespringPre.ofPre A H φ f)
      (StinespringPre.ofPre A H φ f))
    rw [stinespringForm_self]
    exact RCLike.nonneg_iff.mp
      (cp_gram_sum_nonneg φ (StinespringPre.ofPre A H φ f).support
        ⇑(StinespringPre.ofPre A H φ f)) |>.1
  add_left f g h := by
    change stinespringForm φ (StinespringPre.ofPre A H φ (f + g)) _ = _ + _
    rw [map_add]
    exact stinespringForm_add_left φ _ _ _
  smul_left f g r := by
    change stinespringForm φ (StinespringPre.ofPre A H φ (r • f)) _ = _ * _
    rw [map_smul]
    exact stinespringForm_smul_left φ _ _ _

end MetaMathlibExt.Stinespring
end
