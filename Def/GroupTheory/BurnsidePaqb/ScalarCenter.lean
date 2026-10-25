/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/ScalarCenter.lean -/

import Def.GroupTheory.BurnsidePaqb.KillingLemma
import Lemma.Representation.Character.eq.SumRootsCharpoly
/-!
Scalar-center stage of the complete Burnside proof.

Authors: Muse Spark 1.3
Source archive: genai_web_search/tree/users/akiezun/burnside_proof.zip
SHA-256: d9da7df82e467d9fa587892eeef9f51e2b83df0588175653bd1d16264b09dd00

This module is mechanically ported from the audited source `extracted/Burnside/ScalarCenter.lean`.
-/


namespace BurnsidePaqb

variable {G : Type*} [Group G] [Fintype G]

/-- The scalar center: elements acting by scalar matrices. -/
noncomputable def charCenter {V : Type*} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (ρ : Representation ℂ G V) : Subgroup G where
  carrier := { g | ∃ c : ℂ, (ρ g : Module.End ℂ V) = c • 1 }
  one_mem' := ⟨1, by rw [map_one, one_smul]⟩
  mul_mem' := by
    intro a b ha hb
    obtain ⟨c₁, hc₁⟩ := ha
    obtain ⟨c₂, hc₂⟩ := hb
    refine ⟨c₁ * c₂, ?_⟩
    rw [map_mul, hc₁, hc₂, smul_mul_assoc, one_mul, smul_smul]
  inv_mem' := by
    intro g hg
    obtain ⟨c, hc⟩ := hg
    have key : (ρ g⁻¹ : Module.End ℂ V) * (ρ g : Module.End ℂ V) = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    rw [hc, mul_smul_comm, mul_one] at key
    have hc0 : c ≠ 0 := by
      intro hz
      rw [hz, zero_smul] at key
      exact one_ne_zero key.symm
    refine ⟨c⁻¹, ?_⟩
    have hsm := congrArg (c⁻¹ • ·) key
    rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at hsm

end BurnsidePaqb
