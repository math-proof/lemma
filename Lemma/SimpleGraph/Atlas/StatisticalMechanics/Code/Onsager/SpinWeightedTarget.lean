import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.SpinWeightedTarget.Part3
open StatMech StatMech.Onsager


/--
[ons_weightedSpinCharacterSum_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinWeightedTarget.lean)
-/
@[path]
private lemma ons_weightedSpinCharacterSum_const_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x : ℝ}
  {a b : Fin 2} :
-- imply
  ons_weightedSpinCharacterSum L (fun _ => (x : ℂ)) a b = (ons_spinCharacterSum L x a b : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_weightedSpinCharacterSum_const L x a b

/--
[ons_spinCoefficientIdentity_of_weightedRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinWeightedTarget.lean)
-/
@[path]
private lemma ons_spinCoefficientIdentity_of_weightedRoot_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x : ℝ}
-- given
  (hweighted : ons_weightedRootIdentity L)
  (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L)) :
-- imply
  ons_spinCoefficientIdentity L x := by
-- proof
  apply StatMech.Onsager.ons_spinCoefficientIdentity_of_weightedRoot L hweighted hx

/--
[ons_spinShermanRadius_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinWeightedTarget.lean)
-/
@[path]
private lemma ons_spinShermanRadius_pos_eq
  {L : ℕ} :
-- imply
  0 < ons_spinShermanRadius L := by
-- proof
  apply StatMech.Onsager.ons_spinShermanRadius_pos L

/--
[ons_spinKacWardIdentities_of_weightedRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinWeightedTarget.lean)
-/
@[path]
private lemma ons_spinKacWardIdentities_of_weightedRoot_eq
  {beta : ℝ}
-- given
  (hweighted : ∀ (L : ℕ) (hL : 2 < L), letI : Fact (2 < L) := ⟨hL⟩ ons_weightedRootIdentity L) :
-- imply
  ons_spinKacWardIdentities beta := by
-- proof
  apply StatMech.Onsager.ons_spinKacWardIdentities_of_weightedRoot hweighted beta


-- created on 2026-10-23
