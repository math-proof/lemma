/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPhysical.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalC1.Part6
import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSignedPhysical.Part4
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


theorem triangularTorusSeamTwistSign_eq_one_or_neg_one
    (L : Nat) (chi : Fin 2 × Fin 2)
    (edge : Sym2 (ZMod L × ZMod L)) :
    triangularTorusSeamTwistSign L chi edge = 1 ∨
      triangularTorusSeamTwistSign L chi edge = -1 := by
  unfold triangularTorusSeamTwistSign triangularTorusLinearCharacter
  exact neg_one_pow_eq_or Real _

@[simp] theorem abs_triangularTorusSeamTwistSign
    (L : Nat) (chi : Fin 2 × Fin 2)
    (edge : Sym2 (ZMod L × ZMod L)) :
    |triangularTorusSeamTwistSign L chi edge| = 1 := by
  rcases triangularTorusSeamTwistSign_eq_one_or_neg_one L chi edge with h | h
  · rw [h]
    norm_num
  · rw [h]
    norm_num

@[simp] theorem cosh_triangularTorusSeamTwistedCoupling
    (L : Nat) (J1 J2 J3 : Real) (chi : Fin 2 × Fin 2)
    (edge : Sym2 (ZMod L × ZMod L)) :
    Real.cosh (triangularTorusSeamTwistedCoupling L J1 J2 J3 chi edge) =
      Real.cosh (triangularTorusRealEdgeWeight L J1 J2 J3 edge) := by
  rcases triangularTorusSeamTwistSign_eq_one_or_neg_one L chi edge with h | h
  · simp [triangularTorusSeamTwistedCoupling, h]
  · simp [triangularTorusSeamTwistedCoupling, h, Real.cosh_neg]

@[simp] theorem tanh_triangularTorusSeamTwistedCoupling
    (L : Nat) (J1 J2 J3 : Real) (chi : Fin 2 × Fin 2)
    (edge : Sym2 (ZMod L × ZMod L)) :
    Real.tanh (triangularTorusSeamTwistedCoupling L J1 J2 J3 chi edge) =
      triangularTorusSeamTwistSign L chi edge *
        Real.tanh (triangularTorusRealEdgeWeight L J1 J2 J3 edge) := by
  rcases triangularTorusSeamTwistSign_eq_one_or_neg_one L chi edge with h | h
  · simp [triangularTorusSeamTwistedCoupling, h]
  · simp [triangularTorusSeamTwistedCoupling, h, Real.tanh_neg]

theorem tanh_triangularTorusRealEdgeWeight
    (L : Nat) (J1 J2 J3 : Real) :
    (fun edge => Real.tanh
      (triangularTorusRealEdgeWeight L J1 J2 J3 edge)) =
      triangularTorusRealEdgeWeight L
        (Real.tanh J1) (Real.tanh J2) (Real.tanh J3) := by
  funext edge
  unfold triangularTorusRealEdgeWeight
  split_ifs <;> rfl

theorem inhomogeneousEvenSubgraphSum_seamTwist
    (L : Nat) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → Real)
    (chi : Fin 2 × Fin 2) :
    inhomogeneousEvenSubgraphSum (triangularTorusGraph L)
        (fun edge => triangularTorusSeamTwistSign L chi edge * weight edge) =
      triangularTorusWeightedLinearCharacterSum L weight chi := by
  classical
  unfold inhomogeneousEvenSubgraphSum
    triangularTorusWeightedLinearCharacterSum
  apply Finset.sum_congr rfl
  intro F hF
  rw [Finset.prod_mul_distrib, prod_triangularTorusSeamTwistSign]


theorem triangularTorusSeamTwistedPartition_highTemperature
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real)
    (chi : Fin 2 × Fin 2) :
    StatMech.Sharpness.ZJ (triangularTorusGraph L).edgeFinset
        (triangularTorusSeamTwistedCoupling L J1 J2 J3 chi) (fun _ => 0) =
      (2 : Real) ^ (L * L) *
        (Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L) *
        triangularTorusWeightedLinearCharacterSum L
          (triangularTorusRealEdgeWeight L
            (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) chi := by
  rw [triangularTorusIsingPartition_highTemperature]
  have hcard : Fintype.card (ZMod L × ZMod L) = L * L := by
    simp [Fintype.card_prod, ZMod.card]
  rw [hcard]
  simp_rw [cosh_triangularTorusSeamTwistedCoupling]
  rw [prod_cosh_triangularTorusRealEdgeWeight]
  simp_rw [tanh_triangularTorusSeamTwistedCoupling]
  simp_rw [congrFun (tanh_triangularTorusRealEdgeWeight L J1 J2 J3)]
  rw [inhomogeneousEvenSubgraphSum_seamTwist]


end StatMech.FrontierA
