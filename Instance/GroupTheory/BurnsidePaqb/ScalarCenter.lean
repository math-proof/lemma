/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/ScalarCenter.lean -/

import Def.GroupTheory.BurnsidePaqb.KillingLemma
import Lemma.Representation.Character.eq.SumRootsCharpoly
import Def.GroupTheory.BurnsidePaqb.ScalarCenter
/-!
Scalar-center stage of the complete Burnside proof.

Authors: Muse Spark 1.3
Source archive: genai_web_search/tree/users/akiezun/burnside_proof.zip
SHA-256: d9da7df82e467d9fa587892eeef9f51e2b83df0588175653bd1d16264b09dd00

This module is mechanically ported from the audited source `extracted/Burnside/ScalarCenter.lean`.
-/


namespace BurnsidePaqb

variable {G : Type*} [Group G] [Fintype G]

instance charCenter_normal {V : Type*} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (ρ : Representation ℂ G V) : (charCenter ρ).Normal where
  conj_mem := by
    intro n hn h
    obtain ⟨c, hc⟩ := hn
    refine ⟨c, ?_⟩
    have hmul : (ρ (h * n * h⁻¹) : Module.End ℂ V)
        = (ρ h : Module.End ℂ V) * (ρ n : Module.End ℂ V)
          * (ρ h⁻¹ : Module.End ℂ V) := by
      rw [map_mul, map_mul]
    have h1 : (ρ h : Module.End ℂ V) * (ρ h⁻¹ : Module.End ℂ V) = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have hsc : (ρ h : Module.End ℂ V) * (c • 1) * (ρ h⁻¹ : Module.End ℂ V)
        = c • ((ρ h : Module.End ℂ V) * (ρ h⁻¹ : Module.End ℂ V)) := by
      simp only [mul_smul_comm, smul_mul_assoc, mul_one]
    rw [hmul, hc, hsc, h1]

end BurnsidePaqb
