import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalAssembly
open StatMech StatMech.Onsager


/--
[ons_weightedRootIdentity_of_decoratedFormal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalAssembly.lean)
-/
@[path]
private lemma ons_weightedRootIdentity_of_decoratedFormal_eq
  {L : ℕ}
  [Fact (2 < L)]
-- given
  (hformal : ons_decoratedFormalKacWardIdentity L) :
-- imply
  ons_weightedRootIdentity L := by
-- proof
  apply StatMech.Onsager.ons_weightedRootIdentity_of_decoratedFormal L hformal

/--
[ons_spinKacWardIdentities_of_decoratedFormal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalAssembly.lean)
-/
@[path]
private lemma ons_spinKacWardIdentities_of_decoratedFormal_eq
  {beta : ℝ}
-- given
  (hformal : ∀ (L : ℕ) (hL : 2 < L), letI : Fact (2 < L) := ⟨hL⟩ ons_decoratedFormalKacWardIdentity L) :
-- imply
  ons_spinKacWardIdentities beta := by
-- proof
  apply StatMech.Onsager.ons_spinKacWardIdentities_of_decoratedFormal hformal beta


-- created on 2026-10-23
