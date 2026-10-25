import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.Buildings.code.BNPair.ConjugatorProof
open ConjugatorProof


/--
[conjugator_in_target_from_bnpair](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/ConjugatorProof.lean)
-/
@[path]
private lemma conjugator_in_target_from_bnpair_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {ax : BNPairAxioms bp} :
-- imply
  ∀ (S₁ S₂ : Set B_idx) (g : G), (fun x => g * x * g⁻¹) '' bp.standardParabolic S₁ = bp.standardParabolic S₂ → g ∈ bp.standardParabolic S₂ := by
-- proof
  apply ConjugatorProof.conjugator_in_target_from_bnpair bp ax


-- created on 2026-10-23
