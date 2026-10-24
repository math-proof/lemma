import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.DecorationFormalClose
open StatMech StatMech.Onsager


/--
[ons_decoratedFormalKacWardIdentity_of_repeatedEdgeVanishes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalClose.lean)
-/
@[path]
private lemma ons_decoratedFormalKacWardIdentity_of_repeatedEdgeVanishes_eq
-- given
  (hvanish : ons_DecFormalRepeatedEdgeVanishes) :
-- imply
  ∀ (L : ℕ) (hL : 2 < L), letI : Fact (2 < L) := ⟨hL⟩ ons_decoratedFormalKacWardIdentity L := by
-- proof
  apply StatMech.Onsager.ons_decoratedFormalKacWardIdentity_of_repeatedEdgeVanishes hvanish

/--
[ons_spinKacWardIdentities_of_repeatedEdgeVanishes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalClose.lean)
-/
@[path]
private lemma ons_spinKacWardIdentities_of_repeatedEdgeVanishes_eq
  {beta : ℝ}
-- given
  (hvanish : ons_DecFormalRepeatedEdgeVanishes) :
-- imply
  ons_spinKacWardIdentities beta := by
-- proof
  apply StatMech.Onsager.ons_spinKacWardIdentities_of_repeatedEdgeVanishes hvanish beta

/--
[ons_free_energy_of_repeatedEdgeVanishes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalClose.lean)
-/
@[path]
private lemma ons_free_energy_of_repeatedEdgeVanishes_eq
  {beta : ℝ}
-- given
  (hvanish : ons_DecFormalRepeatedEdgeVanishes)
  (hbeta : 0 ≤ beta) :
-- imply
  Filter.Tendsto (ons_torusPressureSeq beta) Filter.atTop (nhds (ons_pressure beta)) := by
-- proof
  apply StatMech.Onsager.ons_free_energy_of_repeatedEdgeVanishes hvanish beta hbeta


-- created on 2026-10-23
