/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/GroupTheory/CyclicSublattice.lean -/


import Def.GroupTheory.CyclicSublattice
import Lemma.Int.IsCyclicSublattice.is.LeAndIsAddCyclic_AddSubgroupOf
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic


/-!
# Examples for cyclic sublattices

Positive and negative examples for `AddSubgroup.IsCyclicSublattice`, each
exercising cyclicity of the quotient rather than containment alone.
-/

/-- Positive example: `⊥` is a cyclic sublattice of `⊤` over `ZMod 4`,
since the quotient is (equivalent to) the cyclic group `ZMod 4`. -/
example : AddSubgroup.IsCyclicSublattice (⊥ : AddSubgroup (ZMod 4)) ⊤ := by
  refine ⟨bot_le, ?_⟩
  have hbot : (⊥ : AddSubgroup (ZMod 4)).addSubgroupOf ⊤ = ⊥ := by
    simp [AddSubgroup.addSubgroupOf]
  let e : ((⊤ : AddSubgroup (ZMod 4)) ⧸ (⊥ : AddSubgroup (ZMod 4)).addSubgroupOf ⊤)
      ≃+ ZMod 4 :=
    (QuotientAddGroup.quotientAddEquivOfEq hbot).trans
      (QuotientAddGroup.quotientBot.trans AddSubgroup.topEquiv)
  exact e.isAddCyclic.mpr inferInstance

/-- Negative example: `⊥` is not a cyclic sublattice of `⊤` over `ℤ × ℤ`,
since the quotient is (equivalent to) the non-cyclic group `ℤ × ℤ`. -/
example : ¬ AddSubgroup.IsCyclicSublattice (⊥ : AddSubgroup (ℤ × ℤ)) ⊤ := by
  intro h
  obtain ⟨-, hcyc⟩ := h
  have hbot : (⊥ : AddSubgroup (ℤ × ℤ)).addSubgroupOf ⊤ = ⊥ := by
    simp [AddSubgroup.addSubgroupOf]
  let e : ((⊤ : AddSubgroup (ℤ × ℤ)) ⧸ (⊥ : AddSubgroup (ℤ × ℤ)).addSubgroupOf ⊤)
      ≃+ ℤ × ℤ :=
    (QuotientAddGroup.quotientAddEquivOfEq hbot).trans
      (QuotientAddGroup.quotientBot.trans AddSubgroup.topEquiv)
  exact not_isAddCyclic_prod_of_infinite_nontrivial ℤ ℤ (e.isAddCyclic.mp hcyc)

