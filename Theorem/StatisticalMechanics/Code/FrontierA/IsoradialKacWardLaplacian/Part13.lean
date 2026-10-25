/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Instance.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacian.Part5


namespace StatMech.FrontierA

open Matrix Finset

open scoped BigOperators

variable {V E D : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]


theorem finiteCRSFWitnessTerm_toFiber
    (conductance transport : V -> V -> Complex) (next : V -> V)
    (S : finiteCRSFCycleSupport next) :
    finiteCRSFWitnessTerm conductance transport S.toFiber =
      S.term conductance transport := by
  have hfixed :
      (∏ v : laplacianPermutationFixedPoint S.ambientPerm,
          conductance v (next v)) =
        ∏ v ∈ (Finset.univ.filter fun v => v ∉ S.carrier),
          conductance v (next v) := by
    symm
    apply Finset.prod_subtype
    intro v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact S.ambientPerm_apply_of_not_mem
    · intro hfixed hv
      exact S.ambientPerm_ne_of_mem hv hfixed
  have hnonfixedSet :
      (Finset.univ.filter fun v => S.ambientPerm v ≠ v) = S.carrier := by
    ext v
    rw [← S.ambientPerm_support]
    simp [Equiv.Perm.mem_support]
  have hcarrierPermuted (v : V) :
      v ∈ S.carrier ↔ S.ambientPerm v ∈ S.carrier := by
    rw [← S.ambientPerm_support]
    exact Equiv.Perm.apply_mem_support.symm
  have hnonfixed :
      (∏ v ∈ (Finset.univ.filter fun v => S.ambientPerm v ≠ v),
          -conductance (S.ambientPerm v) v *
            transport (S.ambientPerm v) v) =
        ∏ v ∈ S.carrier,
          -conductance v (next v) * transport v (next v) := by
    rw [hnonfixedSet]
    apply Finset.prod_equiv S.ambientPerm
    · exact hcarrierPermuted
    · intro v hv
      have himage : S.ambientPerm v ∈ S.carrier :=
        (hcarrierPermuted v).mp hv
      have hnext : next (S.ambientPerm v) = v := by
        rw [← S.ambientPerm_symm_apply_of_mem himage]
        exact S.ambientPerm.symm_apply_apply v
      rw [hnext]
  change Equiv.Perm.sign S.ambientPerm •
      ((∏ v : laplacianPermutationFixedPoint S.ambientPerm,
          conductance v (next v)) *
        ∏ v ∈ (Finset.univ.filter fun v => S.ambientPerm v ≠ v),
          -conductance (S.ambientPerm v) v *
            transport (S.ambientPerm v) v) =
    Equiv.Perm.sign S.ambientPerm •
      ((∏ v ∈ (Finset.univ.filter fun v => v ∉ S.carrier),
          conductance v (next v)) *
        ∏ v ∈ S.carrier,
          -conductance v (next v) * transport v (next v))
  rw [hfixed, hnonfixed]


theorem finiteCRSFCycleSupport.term_eq_atomicCycleSign
    (conductance transport : V -> V -> Complex) (next : V -> V)
    (S : finiteCRSFCycleSupport next) :
    S.term conductance transport =
      (-1 : Complex) ^ S.atomicCycles.card *
        ((∏ v ∈ (Finset.univ.filter fun v => v ∉ S.carrier),
            conductance v (next v)) *
          ∏ v ∈ S.carrier,
            conductance v (next v) * transport v (next v)) := by
  unfold finiteCRSFCycleSupport.term
  rw [S.sign_ambientPerm_eq_atomicCycles]
  simp_rw [neg_mul]
  rw [Finset.prod_neg]
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul Complex, smul_eq_mul]
  have hcast (n : Nat) :
      ((↑(↑((-1 : ℤˣ) ^ n) : ℤ) : Complex)) =
        (-1 : Complex) ^ n := by
    change (((((-1 : ℤˣ) : ℤ) ^ n : ℤ) : Complex)) = _
    rw [Int.cast_pow]
    norm_num
  rw [hcast, pow_add]
  have hcancel :
      (-1 : Complex) ^ S.carrier.card *
          (-1 : Complex) ^ S.carrier.card = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    ((-1 : Complex) ^ S.carrier.card *
          (-1 : Complex) ^ S.atomicCycles.card) *
        ((∏ v ∈ (Finset.univ.filter fun v => v ∉ S.carrier),
            conductance v (next v)) *
          ((-1 : Complex) ^ S.carrier.card *
            ∏ v ∈ S.carrier,
              conductance v (next v) * transport v (next v))) =
      ((-1 : Complex) ^ S.carrier.card *
          (-1 : Complex) ^ S.carrier.card) *
        ((-1 : Complex) ^ S.atomicCycles.card *
          ((∏ v ∈ (Finset.univ.filter fun v => v ∉ S.carrier),
              conductance v (next v)) *
            ∏ v ∈ S.carrier,
              conductance v (next v) * transport v (next v))) := by
        ring
    _ = _ := by rw [hcancel, one_mul]


theorem finiteCRSFCycleSupport.term_eq_atomicCycleHolonomies
    (conductance transport : V -> V -> Complex) (next : V -> V)
    (S : finiteCRSFCycleSupport next) :
    S.term conductance transport =
      (-1 : Complex) ^ S.atomicCycles.card *
        ((∏ v : V, conductance v (next v)) *
          ∏ cycle ∈ S.atomicCycles,
            S.atomicCycleHolonomy transport cycle) := by
  rw [S.term_eq_atomicCycleSign]
  have hinside :
      (∏ v ∈ S.carrier,
          conductance v (next v) * transport v (next v)) =
        (∏ v ∈ S.carrier, conductance v (next v)) *
          ∏ v ∈ S.carrier, transport v (next v) := by
    exact Finset.prod_mul_distrib
  rw [hinside]
  rw [prod_transport_eq_prod_atomicCycleHolonomy transport S]
  have hpartition :
      (∏ v ∈ (Finset.univ.filter fun v => v ∉ S.carrier),
          conductance v (next v)) *
        (∏ v ∈ S.carrier, conductance v (next v)) =
      ∏ v : V, conductance v (next v) := by
    have hcarrierFilter :
        (Finset.univ.filter fun v : V => v ∈ S.carrier) = S.carrier := by
      ext v
      simp
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_not,
      hcarrierFilter] using
      (Finset.prod_filter_mul_prod_filter_not
        (Finset.univ : Finset V) (fun v => v ∉ S.carrier)
        (fun v => conductance v (next v)))
  calc
    (-1 : Complex) ^ S.atomicCycles.card *
        ((∏ v ∈ (Finset.univ.filter fun v => v ∉ S.carrier),
            conductance v (next v)) *
          ((∏ v ∈ S.carrier, conductance v (next v)) *
            ∏ cycle ∈ S.atomicCycles,
              S.atomicCycleHolonomy transport cycle)) =
      (-1 : Complex) ^ S.atomicCycles.card *
        (((∏ v ∈ (Finset.univ.filter fun v => v ∉ S.carrier),
            conductance v (next v)) *
          (∏ v ∈ S.carrier, conductance v (next v))) *
            ∏ cycle ∈ S.atomicCycles,
              S.atomicCycleHolonomy transport cycle) := by ring
    _ = _ := by rw [hpartition]


end StatMech.FrontierA
