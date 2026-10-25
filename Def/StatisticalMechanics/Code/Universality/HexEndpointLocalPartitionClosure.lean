/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalPartitionClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalPartitionClosure


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

noncomputable def hexEndpointLocalPartitionOfCanonicalAtoms
    (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ) (v du : ℂ)
    (atomOf : List ℤ → HexEndpointLocalAtom R.inRegion a h0 v du)
    (mem_atom : ∀ ts ∈ R.endpointCombinedSupportFinset a h0 v du,
      ts ∈ (atomOf ts).piece)
    (atom_subset : ∀ ts ∈ R.endpointCombinedSupportFinset a h0 v du,
      (atomOf ts).piece ⊆ R.endpointCombinedSupportFinset a h0 v du)
    (overlap_eq : ∀ x (_hx : x ∈ R.endpointCombinedSupportFinset a h0 v du)
      y (_hy : y ∈ R.endpointCombinedSupportFinset a h0 v du) z,
      z ∈ (atomOf x).piece → z ∈ (atomOf y).piece →
        atomOf x = atomOf y) :
    HexEndpointLocalPartition R a h0 v du := by
  classical
  let S := R.endpointCombinedSupportFinset a h0 v du
  let atoms := S.image atomOf
  refine {
    atoms := atoms
    cover := ?_
    disjoint := ?_ }
  · ext z
    constructor
    · intro hz
      rw [Finset.mem_biUnion] at hz
      obtain ⟨A, hA, hzA⟩ := hz
      simp only [atoms, Finset.mem_image] at hA
      obtain ⟨x, hx, rfl⟩ := hA
      exact atom_subset x hx hzA
    · intro hz
      rw [Finset.mem_biUnion]
      refine ⟨atomOf z, ?_, mem_atom z hz⟩
      simp only [atoms, Finset.mem_image]
      exact ⟨z, hz, rfl⟩
  · intro A hA B hB hAB
    change A ∈ atoms at hA
    change B ∈ atoms at hB
    simp only [atoms, Finset.mem_image] at hA hB
    obtain ⟨x, hx, rfl⟩ := hA
    obtain ⟨y, hy, rfl⟩ := hB
    change Disjoint (atomOf x).piece (atomOf y).piece
    rw [Finset.disjoint_left]
    intro z hzx hzy
    exact hAB (overlap_eq x hx y hy z hzx hzy)

end
end StatMech.Universality
