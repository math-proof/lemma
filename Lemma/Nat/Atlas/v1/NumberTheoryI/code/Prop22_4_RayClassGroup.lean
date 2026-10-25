import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.NumberTheoryI.code.Prop22_4_RayClassGroup
open RayClassField GlobalCFT


/--
[proposition_22_4_equivalence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop22_4_RayClassGroup.lean)
-/
@[path]
lemma proposition_22_4_equivalence
  [Field K]
  [NumberField K] :
-- imply
  Equivalence (CongruenceSubgroupPair.IsEquiv (K := K)) where refl :=
-- proof
  CongruenceSubgroupPair.isEquiv_refl
    symm := CongruenceSubgroupPair.IsEquiv.symm'
    trans := fun h₁ h₂ => h₁.trans' h₂


-- created on 2026-10-23
