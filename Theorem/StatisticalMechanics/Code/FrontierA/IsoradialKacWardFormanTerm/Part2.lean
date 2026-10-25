/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardFormanTerm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacian.Part17
import Def.StatisticalMechanics.Code.FrontierA.IsoradialKacWardFormanTerm.Part2


namespace StatMech.FrontierA

open Finset

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem finiteCRSFSupportTransport_eq_prod_atomicCycleCoefficient
    (transport : V -> V -> Complex) {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    finiteCRSFSupportTransport transport S =
      ∏ cycle ∈ S.atomicCycles,
        finiteCRSFAtomicCycleCoefficient transport S cycle := by
  unfold finiteCRSFSupportTransport finiteCRSFAtomicCycleCoefficient
  rw [S.sign_ambientPerm_eq_atomicCycles]
  rw [Finset.prod_neg]
  rw [finiteCRSF_prod_transport_eq_prod_atomicCycleHolonomy]
  rw [Finset.prod_neg]
  simp only [Units.smul_def, zsmul_eq_mul]
  have hsignCast (n : Nat) :
      (((↑((-1 : ℤˣ) ^ n) : ℤ) : Complex)) = (-1 : Complex) ^ n := by
    change ((((-1 : ℤ) ^ n : ℤ) : Complex)) = (-1 : Complex) ^ n
    push_cast
    rfl
  rw [hsignCast]
  rw [pow_add]
  have hcancel :
      (-1 : Complex) ^ S.carrier.card *
          (-1 : Complex) ^ S.carrier.card = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc
    ((-1 : Complex) ^ S.carrier.card *
          (-1 : Complex) ^ S.atomicCycles.card) *
        ((-1 : Complex) ^ S.carrier.card *
          ∏ cycle ∈ S.atomicCycles,
            finiteCRSFAtomicCycleHolonomy transport S cycle) =
      ((-1 : Complex) ^ S.carrier.card *
          (-1 : Complex) ^ S.carrier.card) *
        ((-1 : Complex) ^ S.atomicCycles.card *
          ∏ cycle ∈ S.atomicCycles,
            finiteCRSFAtomicCycleHolonomy transport S cycle) := by ring
    _ = _ := by rw [hcancel, one_mul]


theorem finiteCRSF_nonfixed_product_reindex
    (conductance transport : V -> V -> Complex) {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    (∏ v ∈ (Finset.univ.filter fun v => S.ambientPerm v ≠ v),
        -conductance (S.ambientPerm v) v *
          transport (S.ambientPerm v) v) =
      ∏ v ∈ S.carrier,
        -conductance v (next v) * transport v (next v) := by
  rw [show (Finset.univ.filter fun v => S.ambientPerm v ≠ v) =
      S.carrier by
    simpa [Equiv.Perm.mem_support] using S.ambientPerm_support]
  rw [S.ambientPerm.prod_comp' S.carrier
    (fun v w => -conductance v w * transport v w)]
  · apply Finset.prod_congr rfl
    intro v hv
    rw [S.ambientPerm_symm_apply_of_mem hv]
  · intro v hv
    rw [← S.ambientPerm_support]
    exact Equiv.Perm.mem_support.mpr hv


theorem finiteCRSF_fixed_product_eq_complement
    (conductance : V -> V -> Complex) {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    (∏ v : laplacianPermutationFixedPoint S.ambientPerm,
        conductance v (next v)) =
      ∏ v : {v : V // v ∉ S.carrier}, conductance v (next v) := by
  exact Fintype.prod_equiv (finiteCRSFFixedPointEquivComplement S)
    (fun v : laplacianPermutationFixedPoint S.ambientPerm =>
      conductance v (next v))
    (fun v : {v : V // v ∉ S.carrier} => conductance v (next v))
    (fun _ => rfl)


theorem finiteCRSFWitnessTerm_toFiber_eq_outgoing_mul_transport
    (conductance transport : V -> V -> Complex) {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    finiteCRSFWitnessTerm conductance transport S.toFiber =
      finiteCRSFOutgoingConductance conductance next *
        finiteCRSFSupportTransport transport S := by
  unfold finiteCRSFWitnessTerm finiteCRSFOutgoingConductance
    finiteCRSFSupportTransport
  change Equiv.Perm.sign S.ambientPerm •
      ((∏ v : laplacianPermutationFixedPoint S.ambientPerm,
          conductance v (next v)) *
        ∏ v ∈ (Finset.univ.filter fun v => S.ambientPerm v ≠ v),
          -conductance (S.ambientPerm v) v *
            transport (S.ambientPerm v) v) = _
  rw [finiteCRSF_fixed_product_eq_complement conductance S]
  rw [finiteCRSF_nonfixed_product_reindex conductance transport S]
  rw [show (∏ v ∈ S.carrier,
      -conductance v (next v) * transport v (next v)) =
        ∏ v ∈ S.carrier,
          conductance v (next v) * (-transport v (next v)) by
    apply Finset.prod_congr rfl
    intro v _
    ring]
  rw [Finset.prod_mul_distrib]
  rw [← mul_assoc]
  rw [← Finset.prod_subtype S.carrierᶜ (by simp)
    (fun v => conductance v (next v))]
  rw [Finset.prod_compl_mul_prod]
  exact (mul_smul_comm (Equiv.Perm.sign S.ambientPerm)
    (∏ v : V, conductance v (next v))
    (∏ v ∈ S.carrier, -transport v (next v))).symm


theorem det_finiteTwistedLaplacian_eq_sum_outgoing_mul_cycleTransport
    (conductance transport : V -> V -> Complex) :
    (finiteTwistedLaplacian conductance transport).det =
      ∑ next : V -> V,
        finiteCRSFOutgoingConductance conductance next *
          ∑ S : finiteCRSFCycleSupport next,
            finiteCRSFSupportTransport transport S := by
  rw [det_finiteTwistedLaplacian_eq_sum_finiteCRSFCycleSupport]
  apply Finset.sum_congr rfl
  intro next _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  exact finiteCRSFWitnessTerm_toFiber_eq_outgoing_mul_transport
    conductance transport S


theorem det_finiteTwistedLaplacian_eq_sum_atomicCycleCoefficients
    (conductance transport : V -> V -> Complex) :
    (finiteTwistedLaplacian conductance transport).det =
      ∑ next : V -> V,
        finiteCRSFOutgoingConductance conductance next *
          ∑ S : finiteCRSFCycleSupport next,
            ∏ cycle ∈ S.atomicCycles,
              finiteCRSFAtomicCycleCoefficient transport S cycle := by
  rw [det_finiteTwistedLaplacian_eq_sum_outgoing_mul_cycleTransport]
  apply Finset.sum_congr rfl
  intro next _
  congr 1
  apply Finset.sum_congr rfl
  intro S _
  exact finiteCRSFSupportTransport_eq_prod_atomicCycleCoefficient transport S

end StatMech.FrontierA
