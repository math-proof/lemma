/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointMirrorOrbitBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthBoundaryWinding.Part4
import Def.StatisticalMechanics.Code.Universality.HexEndpointMirrorOrbitBoundary.Part4


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

namespace HexEndpointMirrorOrbitData

variable {I K V : Type*} [Fintype I] [Fintype K]

variable [DecidableEq I] [DecidableEq K] [DecidableEq V]

variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}

variable {P : D.InteriorPairing}

variable {C : HexEndpointBoundaryCore R h0 D P}

variable (H : HexEndpointMirrorOrbitData (I := I) (K := K) C)


variable (Kc : DCSClassification H)

theorem pairClassMass_nonneg
    (hpairs : ∀ i, 0 ≤ (H.pairs i).mass)
    (k : HexPairedBoundaryClass) :
    0 ≤ H.pairClassMass Kc k := by
  classical
  unfold pairClassMass
  apply Finset.sum_nonneg
  intro i _
  split
  · exact mul_nonneg (by norm_num) (hpairs i)
  · exact le_rfl

theorem fixedMass_nonneg : 0 ≤ H.fixedMass := by
  unfold fixedMass
  exact Finset.sum_nonneg (fun k _ => (H.fixed k).mass_nonneg)

theorem dcs_values_nonneg
    (hpairs : ∀ i, 0 ≤ (H.pairs i).mass) :
    0 ≤ H.dcsLam Kc ∧ 0 ≤ H.dcsTau Kc ∧ 0 ≤ H.dcsUps Kc := by
  exact ⟨H.pairClassMass_nonneg Kc hpairs .side,
    H.pairClassMass_nonneg Kc hpairs .slant,
    add_nonneg (H.pairClassMass_nonneg Kc hpairs .top)
      H.fixedMass_nonneg⟩

theorem pair_term_decompose (i : I) :
    2 * Real.cos (H.pairs i).angle * (H.pairs i).mass =
      hexCl * (if Kc.classOf i = .side then 2 * (H.pairs i).mass else 0) +
      hexCt * (if Kc.classOf i = .slant then 2 * (H.pairs i).mass else 0) +
      (if Kc.classOf i = .top then 2 * (H.pairs i).mass else 0) := by
  rw [Kc.cos_angle i]
  cases hclass : Kc.classOf i <;> simp [hclass] <;> ring

theorem totalContribution_decompose :
    H.totalContribution =
      hexCl * H.dcsLam Kc + hexCt * H.dcsTau Kc + H.dcsUps Kc := by
  classical
  unfold totalContribution dcsLam dcsTau dcsUps pairClassMass fixedMass
  calc
    (∑ i : I, 2 * Real.cos (H.pairs i).angle * (H.pairs i).mass) +
        ∑ k : K, (H.fixed k).mass =
      (∑ i : I,
        (hexCl * (if Kc.classOf i = .side then 2 * (H.pairs i).mass else 0) +
          hexCt * (if Kc.classOf i = .slant then 2 * (H.pairs i).mass else 0) +
          (if Kc.classOf i = .top then 2 * (H.pairs i).mass else 0))) +
        ∑ k : K, (H.fixed k).mass := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact H.pair_term_decompose Kc i
    _ = hexCl * (∑ i : I,
          if Kc.classOf i = .side then 2 * (H.pairs i).mass else 0) +
        hexCt * (∑ i : I,
          if Kc.classOf i = .slant then 2 * (H.pairs i).mass else 0) +
        ((∑ i : I,
          if Kc.classOf i = .top then 2 * (H.pairs i).mass else 0) +
          ∑ k : K, (H.fixed k).mass) := by
      simp only [Finset.sum_add_distrib]
      repeat rw [← Finset.mul_sum]
      ring


theorem normalized_dcs_identity :
    hexCl * H.dcsLam Kc + hexCt * H.dcsTau Kc + H.dcsUps Kc = 1 := by
  rw [← H.totalContribution_decompose Kc]
  exact H.totalContribution_eq_one

end HexEndpointMirrorOrbitData
end
end StatMech.Universality
