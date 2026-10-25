/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterAgreementMarginalRatio.Part2
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeActual.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeMarginalRank.Part2
open Finset SimpleGraph


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem ghsiSubsetMarginalMass_eq_common_mul_agreementMarginal
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    {M P : Finset V} (hPM : P ⊆ M) :
    ghsiSubsetMarginalMass G J hf M P =
      ((4 * Fintype.card (ConfigSpace V) : Real) *
          (ZJ G.edgeFinset J hf) ^ 2) *
        ghsiAgreementMarginalProb G J hf M P := by
  classical
  let C : Real := 4 * Fintype.card (ConfigSpace V)
  have hscale (A : Finset V) :
      ghsiSubsetMass G J hf A =
        C * ghsiFibreMass G J hf (agreementConfigFinsetEquiv.symm A) := by
    have h := ghsiSubsetMass_agreeFinset_eq_mul_fibreMass
      G J hf (agreementConfigFinsetEquiv.symm A)
    have hagree :
        ghsLAgreeFinset (agreementConfigFinsetEquiv.symm A) = A :=
      agreementConfigFinsetEquiv.apply_symm_apply A
    rw [hagree] at h
    exact h
  have hreindex :
      (∑ S ∈ Mᶜ.powerset,
          ghsiFibreMass G J hf
            (agreementConfigFinsetEquiv.symm (P ∪ S))) =
        ∑ q ∈ (Finset.univ : Finset (ConfigSpace V)).filter
            (fun q => ghsLAgreeFinset q ∩ M = P),
          ghsiFibreMass G J hf q := by
    apply Finset.sum_bij
      (fun S _ => agreementConfigFinsetEquiv.symm (P ∪ S))
    · intro S hS
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hSc : S ⊆ Mᶜ := Finset.mem_powerset.mp hS
      have hagree :
          ghsLAgreeFinset
              (agreementConfigFinsetEquiv.symm (P ∪ S)) = P ∪ S :=
        agreementConfigFinsetEquiv.apply_symm_apply (P ∪ S)
      rw [hagree]
      ext v
      simp only [mem_inter, mem_union]
      constructor
      · rintro ⟨hvP | hvS, hvM⟩
        · exact hvP
        · exact False.elim ((mem_compl.mp (hSc hvS)) hvM)
      · intro hvP
        exact ⟨Or.inl hvP, hPM hvP⟩
    · intro S hS T hT hEq
      apply Finset.ext
      intro v
      have hsets : P ∪ S = P ∪ T := by
        exact agreementConfigFinsetEquiv.symm.injective hEq
      have hSc : S ⊆ Mᶜ := Finset.mem_powerset.mp hS
      have hTc : T ⊆ Mᶜ := Finset.mem_powerset.mp hT
      constructor
      · intro hvS
        have hvU : v ∈ P ∪ T := by
          rw [← hsets]
          exact mem_union_right P hvS
        rcases mem_union.mp hvU with hvP | hvT
        · exact False.elim ((mem_compl.mp (hSc hvS)) (hPM hvP))
        · exact hvT
      · intro hvT
        have hvU : v ∈ P ∪ S := by
          rw [hsets]
          exact mem_union_right P hvT
        rcases mem_union.mp hvU with hvP | hvS
        · exact False.elim ((mem_compl.mp (hTc hvT)) (hPM hvP))
        · exact hvS
    · intro q hq
      have hqM : ghsLAgreeFinset q ∩ M = P :=
        (Finset.mem_filter.mp hq).2
      let S := ghsLAgreeFinset q \ M
      have hSc : S ⊆ Mᶜ := by
        intro v hv
        exact mem_compl.mpr (mem_sdiff.mp hv).2
      refine ⟨S, Finset.mem_powerset.mpr hSc, ?_⟩
      apply agreementConfigFinsetEquiv.injective
      rw [Equiv.apply_symm_apply]
      change P ∪ S = ghsLAgreeFinset q
      ext v
      simp only [mem_union]
      constructor
      · intro hv
        rcases hv with hvP | hvS
        · have hvPi : v ∈ ghsLAgreeFinset q ∩ M := by
            rw [hqM]
            exact hvP
          exact (mem_inter.mp hvPi).1
        · exact (mem_sdiff.mp hvS).1
      · intro hvq
        by_cases hvM : v ∈ M
        · left
          have hi : v ∈ ghsLAgreeFinset q ∩ M :=
            mem_inter.mpr ⟨hvq, hvM⟩
          rw [hqM] at hi
          exact hi
        · right
          exact mem_sdiff.mpr ⟨hvq, hvM⟩
    · intro S hS
      rfl
  unfold ghsiSubsetMarginalMass ghsiAgreementMarginalProb
  simp_rw [hscale]
  rw [← Finset.mul_sum, hreindex]
  simp_rw [ghsiAgreementProb]
  rw [← Finset.sum_div]
  have hZ : ZJ G.edgeFinset J hf ≠ 0 := (ZJ_pos _ _ _).ne'
  field_simp [hZ]
  ring


end
end StatMech.Ising
