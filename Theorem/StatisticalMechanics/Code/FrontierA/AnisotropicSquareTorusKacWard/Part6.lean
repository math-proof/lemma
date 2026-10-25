/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AnisotropicSquareTorusKacWard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalMultiaffine
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonGlobalReduction.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Def.StatisticalMechanics.Code.FrontierA.AnisotropicSquareTorusKacWard.Part6
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


theorem anisotropicSquareEdgeWeight_port
    (L : Nat) [Fact (2 < L)] (x y : Complex) (d : ons_Dart L) :
    anisotropicSquareEdgeWeight L x y (ons_portEdge L d) =
      squareTorusDirectionWeight x y d.2 := by
  rcases d with ⟨p, mu⟩
  fin_cases mu
  · rw [anisotropicSquareEdgeWeight, if_pos]
    · rfl
    · exact ⟨p, rfl⟩
  · rw [anisotropicSquareEdgeWeight, if_neg]
    · rfl
    · rintro ⟨q, hq⟩
      have h := (ons_portEdge_eq_iff L (p, 1) (q, 0)).mp hq.symm
      rcases h with h | h
      · have := congrArg Prod.snd h
        norm_num at this
      · have := congrArg Prod.snd h
        simp [ons_dartRev] at this
  · rw [anisotropicSquareEdgeWeight, if_pos]
    · rfl
    · refine ⟨(p.1 - 1, p.2), ?_⟩
      exact ons_portEdge_west_eq_horizontal L p
  · rw [anisotropicSquareEdgeWeight, if_neg]
    · rfl
    · rintro ⟨q, hq⟩
      have h := (ons_portEdge_eq_iff L (p, 3) (q, 0)).mp hq.symm
      rcases h with h | h
      · have := congrArg Prod.snd h
        exact (by decide : (0 : Fin 4) ≠ 3) this
      · have := congrArg Prod.snd h
        simp [ons_dartRev] at this

theorem weightedPhase_anisotropicSquareEdgeWeight
    (L : Nat) [Fact (2 < L)] (x y omega u v : Complex) :
    ons_KWmatWeightedPhase L (anisotropicSquareEdgeWeight L x y)
        omega u v =
      anisotropicSquareKWMatrixPhase L x y omega u v := by
  ext d₂ d₁
  unfold ons_KWmatWeightedPhase ons_KWmatWeighted
    anisotropicSquareKWMatrixPhase
  rw [anisotropicSquareEdgeWeight_port]


theorem anisotropicSquare_weightedSpin_sq_eq_det
    (L : Nat) [Fact (2 < L)] (x y : Complex) (a b : Fin 2) :
    ons_weightedSpinCharacterSum L
        (anisotropicSquareEdgeWeight L x y) a b ^ 2 =
      (1 - anisotropicSquareKWMatrixPhase L x y ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)).det := by
  rw [← weightedPhase_anisotropicSquareEdgeWeight]
  exact squareTorus_weightedSpin_sq_eq_det L
    (anisotropicSquareEdgeWeight L x y) a b


theorem anisotropicSquare_weightedSpin_sq_eq_cosProduct
    (L : Nat) [Fact (2 < L)] (x y : Complex) (a b : Fin 2) :
    ons_weightedSpinCharacterSum L
        (anisotropicSquareEdgeWeight L x y) a b ^ 2 =
      ∏ j : ZMod L × ZMod L,
        ((1 + x ^ 2) * (1 + y ^ 2) -
          2 * x * (1 - y ^ 2) *
            Real.cos (2 * Real.pi *
              (j.1.val + (a.val : Real) / 2) / L) -
          2 * y * (1 - x ^ 2) *
            Real.cos (2 * Real.pi *
              (j.2.val + (b.val : Real) / 2) / L)) := by
  letI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  rw [anisotropicSquare_weightedSpin_sq_eq_det]
  exact anisotropicSquareKWMatrixPhase_det_eq_cosProduct L x y a b

theorem anisotropicSquareFourierFactor_eq_triangularHighTempSymbol
    (J₁ J₂ k q : Real) :
    (1 + Real.tanh J₁ ^ 2) * (1 + Real.tanh J₂ ^ 2) -
        2 * Real.tanh J₁ * (1 - Real.tanh J₂ ^ 2) * Real.cos k -
        2 * Real.tanh J₂ * (1 - Real.tanh J₁ ^ 2) * Real.cos q =
      triangularIsingHighTempSymbol J₁ J₂ 0 k q := by
  simp only [triangularIsingHighTempSymbol, Real.tanh_zero, pow_two,
    mul_zero, zero_mul, add_zero, sub_zero]
  ring


theorem anisotropicSquare_weightedSpin_tanh_sq_eq_triangularProduct
    (L : Nat) [Fact (2 < L)] (J₁ J₂ : Real) (a b : Fin 2) :
    ons_weightedSpinCharacterSum L
        (anisotropicSquareEdgeWeight L (Real.tanh J₁) (Real.tanh J₂)) a b ^ 2 =
      ∏ j : ZMod L × ZMod L,
        (triangularIsingHighTempSymbol J₁ J₂ 0
          (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
          (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) : Complex) := by
  rw [anisotropicSquare_weightedSpin_sq_eq_cosProduct]
  apply Finset.prod_congr rfl
  intro j _
  norm_cast
  exact anisotropicSquareFourierFactor_eq_triangularHighTempSymbol
    J₁ J₂
    (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
    (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L)


theorem anisotropicSquare_normalizedSpin_tanh_sq_eq_triangularProduct
    (L : Nat) [Fact (2 < L)] (J₁ J₂ : Real) (a b : Fin 2) :
    (((Real.cosh J₁ * Real.cosh J₂) ^ (L * L) : Real) *
        ons_weightedSpinCharacterSum L
          (anisotropicSquareEdgeWeight L (Real.tanh J₁) (Real.tanh J₂)) a b) ^ 2 =
      ∏ j : ZMod L × ZMod L,
        (triangularIsingSymbol J₁ J₂ 0
          (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
          (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) : Complex) := by
  let C : Real := Real.cosh J₁ * Real.cosh J₂
  let W : Complex := ons_weightedSpinCharacterSum L
    (anisotropicSquareEdgeWeight L (Real.tanh J₁) (Real.tanh J₂)) a b
  have hW : W ^ 2 =
      ∏ j : ZMod L × ZMod L,
        (triangularIsingHighTempSymbol J₁ J₂ 0
          (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
          (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) : Complex) :=
    anisotropicSquare_weightedSpin_tanh_sq_eq_triangularProduct L J₁ J₂ a b
  have hfactor (j : ZMod L × ZMod L) :
      (triangularIsingSymbol J₁ J₂ 0
          (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
          (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) : Complex) =
        (C ^ 2 : Real) *
          triangularIsingHighTempSymbol J₁ J₂ 0
            (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
            (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) := by
    have hnorm := triangularIsingHighTempSymbol_mul_cosh_sq J₁ J₂ 0
      (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
      (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L)
    simp only [Real.cosh_zero, one_pow, mul_one] at hnorm
    have hreal :
        triangularIsingSymbol J₁ J₂ 0
            (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
            (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) =
          C ^ 2 * triangularIsingHighTempSymbol J₁ J₂ 0
            (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
            (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) := by
      rw [← hnorm]
      dsimp only [C]
      ring
    exact_mod_cast hreal
  change (((C ^ (L * L) : Real) : Complex) * W) ^ 2 = _
  rw [mul_pow, hW]
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_prod, ZMod.card]
  push_cast
  have hpow : ((C : Complex) ^ (L * L)) ^ 2 =
      ((C : Complex) ^ 2) ^ (L * L) := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  rw [hpow]


end StatMech.FrontierA
