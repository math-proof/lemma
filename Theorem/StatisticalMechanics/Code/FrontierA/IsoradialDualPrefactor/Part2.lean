/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.SimpleGraphCellularRibbonEmbedding.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsoradialDualPrefactor


namespace StatMech.FrontierA

open Finset

open scoped BigOperators


variable {E : Type*} [Fintype E] [DecidableEq E]

omit [DecidableEq E] in


theorem kwIsoradialDualityNormalization_mul_prefactor
    {Vertex : Type*} [Fintype Vertex]
    (theta : E -> Real) (exceptional : Vertex -> Bool)
    (htheta : forall edge, 0 < theta edge)
    (htheta' : forall edge, theta edge < Real.pi / 2) :
    kwIsoradialDualityNormalization Vertex theta *
        criticalKacWardRibbonPrefactor theta exceptional =
      (-1 : Complex) ^ Fintype.card Vertex *
        (2 : Complex) ^ Fintype.card E *
        (∏ vertex : Vertex, coneQuarterPhase exceptional vertex) *
        ∏ edge : E, (Real.cos (theta edge) : Complex) := by
  have htwo : (2 : Complex) ^ Fintype.card Vertex ≠ 0 := by norm_num
  have hedge (edge : E) :
      (1 + Real.cos (theta edge) : Complex) ≠ 0 := by
    have hcos : 0 < Real.cos (theta edge) :=
      Real.cos_pos_of_mem_Ioo
        ⟨by nlinarith [Real.pi_pos, htheta edge], htheta' edge⟩
    have hreal : 1 + Real.cos (theta edge) ≠ 0 :=
      ne_of_gt (by linarith)
    exact_mod_cast hreal
  have hproducts :
      (∏ edge : E, (1 + (Real.cos (theta edge) : Complex))) *
          kwLaplacianEdgePrefactor theta =
        ∏ edge : E, (Real.cos (theta edge) : Complex) := by
    unfold kwLaplacianEdgePrefactor
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro edge _
    rw [Complex.ofReal_add, Complex.ofReal_one]
    rw [div_eq_mul_inv]
    calc
      (1 + (Real.cos (theta edge) : Complex)) *
          ((Real.cos (theta edge) : Complex) *
            (1 + (Real.cos (theta edge) : Complex))⁻¹) =
        (Real.cos (theta edge) : Complex) *
          ((1 + (Real.cos (theta edge) : Complex)) *
            (1 + (Real.cos (theta edge) : Complex))⁻¹) := by ring
      _ = (Real.cos (theta edge) : Complex) := by
        rw [mul_inv_cancel₀ (hedge edge), mul_one]
  unfold kwIsoradialDualityNormalization
    criticalKacWardRibbonPrefactor kwEulerPowerPrefactor
  rw [← hproducts]
  field_simp


theorem prod_coneQuarterPhase
    (Vertex : Type*) [Fintype Vertex]
    (exceptional : Vertex -> Bool) :
    (∏ vertex : Vertex, coneQuarterPhase exceptional vertex) =
      Complex.I ^ Fintype.card Vertex *
        (-1 : Complex) ^ coneExceptionCount exceptional := by
  classical
  have hlocal (vertex : Vertex) :
      coneQuarterPhase exceptional vertex =
        Complex.I * if exceptional vertex then (-1 : Complex) else 1 := by
    cases h : exceptional vertex <;>
      simp [coneQuarterPhase, h]
  calc
    (∏ vertex : Vertex, coneQuarterPhase exceptional vertex) =
        ∏ vertex : Vertex,
          Complex.I * if exceptional vertex then (-1 : Complex) else 1 := by
      apply Finset.prod_congr rfl
      intro vertex _
      exact hlocal vertex
    _ = (∏ _vertex : Vertex, Complex.I) *
        ∏ vertex : Vertex,
          if exceptional vertex then (-1 : Complex) else 1 := by
      rw [Finset.prod_mul_distrib]
    _ = Complex.I ^ Fintype.card Vertex *
        (-1 : Complex) ^ coneExceptionCount exceptional := by
      rw [coneExceptionCount, Finset.prod_ite]
      simp


theorem coneExceptionCount_mod_two_eq_sum
    (Vertex : Type*) [Fintype Vertex]
    (exceptional : Vertex -> Bool) (coneIndex : Vertex -> Nat)
    (hexceptional : forall vertex,
      exceptional vertex = true ↔ coneIndex vertex % 2 = 1) :
    coneExceptionCount exceptional % 2 =
      (∑ vertex : Vertex, coneIndex vertex) % 2 := by
  classical
  have hterm (vertex : Vertex) :
      (if exceptional vertex then 1 else 0) = coneIndex vertex % 2 := by
    cases h : exceptional vertex
    · have hv := hexceptional vertex
      simp [h] at hv
      have hlt := Nat.mod_lt (coneIndex vertex) (by omega : 0 < 2)
      simp
      omega
    · have hv := (hexceptional vertex).mp h
      simp [hv]
  have hcount : coneExceptionCount exceptional =
      ∑ vertex : Vertex, if exceptional vertex then 1 else 0 := by
    simp [coneExceptionCount]
  rw [hcount]
  simp_rw [hterm]
  exact Nat.ModEq.sum fun vertex _ => Nat.mod_modEq (coneIndex vertex) 2


end StatMech.FrontierA
