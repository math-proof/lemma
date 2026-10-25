-- Carved from Lemma/Definitions/Def_ValuationSubring_ReduceAt.lean: instance decls only.
import Mathlib
import Lemma.WeierstrassCurve.ReductionMap

set_option autoImplicit false

open IsLocalRing Polynomial

namespace ValuationSubring

section ResidueAlgClosed

variable {L : Type*} [Field L] (A : ValuationSubring L)

instance instIsAlgClosedResidueField [IsAlgClosed L] :
    IsAlgClosed (ResidueField A) := by
  refine IsAlgClosed.of_exists_root _ (fun f hf_monic hf_irr => ?_)

  have hf_lifts : f ∈ lifts (residue A) := by
    rw [lifts_iff_coeff_lifts]
    exact fun n => residue_surjective (f.coeff n)
  obtain ⟨g, hg_map, -, hg_monic⟩ := lifts_and_degree_eq_and_monic hf_lifts hf_monic

  have hgL_monic : (g.map (algebraMap A L)).Monic := hg_monic.map _
  have hgL_deg : (g.map (algebraMap A L)).degree ≠ 0 := by
    rw [hg_monic.degree_map]
    intro h0

    have hg_nat : g.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h0)
    have hf_deg : f.natDegree = 0 := by
      rw [← hg_map, hg_monic.natDegree_map]
      exact hg_nat
    have hf1 : f = 1 := (hf_monic.natDegree_eq_zero).mp hf_deg
    exact hf_irr.not_isUnit (by rw [hf1]; exact isUnit_one)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hgL_deg

  have hα_int : IsIntegral A α := by
    refine ⟨g, hg_monic, ?_⟩
    rwa [IsRoot.def, eval_map] at hα
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hα_int

  refine ⟨residue A a, ?_⟩
  have hga : g.eval a = 0 := by
    have : algebraMap A L (g.eval a) = 0 := by
      have hcomm : algebraMap A L (g.eval a) = (g.map (algebraMap A L)).eval α := by
        rw [← ha, eval_map, eval₂_hom]
      rw [hcomm]
      exact hα
    exact (map_eq_zero_iff _ Subtype.coe_injective).mp this
  have : f.eval (residue A a) = residue A (g.eval a) := by
    rw [← hg_map, eval_map, eval₂_hom]
  rw [this, hga, map_zero]

variable {A}

end ResidueAlgClosed

variable {L : Type*} [Field L]


end ValuationSubring
