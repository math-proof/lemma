/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentExchangeSupportTag.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCycleComponentExchange.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamComponentExchangeSupportTag
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]

noncomputable def componentExchangeSupportTag
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero) :
    leftRowSupportIndex ends m j k l zero →
      rightRowData ends m j k l zero := fun d => by
  classical
  let K := d.1
  let A := edgeComponent ends K zero
  let R := exchangeFirstRow ends K (m \ K) k zero
  have hmap := componentExchange_maps_leftRowSupport
    (ends := ends) (m := m) (K := K) (j := j) (k := k) (l := l)
    (zero := zero) hloop d.2.1 hjk hkl hk0 d.2.2
  have hRsub : R ⊆ m := by simpa only [R, K] using hmap.1
  have hRright : RightRowSupport ends m j k l zero R := by
    simpa only [R, K] using hmap.2
  have hAsubK : A ⊆ K := by
    intro i hi
    change i ∈ edgeComponent ends K zero at hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hBsub : edgeComponent ends (m \ K) k ⊆ m \ K := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hPsub : K \ A ⊆ R := by
    intro i hi
    exact Finset.mem_union_left _ hi
  have hAsubCompl : A ⊆ m \ R := by
    intro i hiA
    refine Finset.mem_sdiff.mpr ⟨d.2.1 (hAsubK hiA), ?_⟩
    intro hiR
    rcases Finset.mem_union.mp hiR with hiKA | hiB
    · exact (Finset.mem_sdiff.mp hiKA).2 hiA
    · exact (Finset.mem_sdiff.mp (hBsub hiB)).2 (hAsubK hiA)
  have hAsrc : sources ends A = ∅ := by
    simpa only [A, K] using
      componentExchange_zeroComponent_source_empty hloop d.2.1 hjk d.2.2
  have hPsrc : sources ends (K \ A) = {j, k} := by
    rw [sources_sdiff_of_subset hAsubK, d.2.2.1, hAsrc]
    simp
  exact ⟨⟨R, hRsub, hRright⟩,
    ⟨⟨K \ A, hPsub, hPsrc⟩, ⟨A, hAsubCompl, hAsrc⟩⟩⟩


end StatMech.GrahamGHS.FourColor
