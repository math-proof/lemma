/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFiniteSpectralBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSquareTorusAdapter.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSymbolReduction.Part2
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Onsager

theorem quantumIsing_sinh_neg_log
    {x : Real} (hx : 0 < x) :
    Real.sinh (-Real.log x) = (1 - x ^ 2) / (2 * x) := by
  rw [Real.sinh_eq, Real.exp_neg, neg_neg, Real.exp_log hx]
  field_simp [hx.ne']


theorem quantumIsingVerticalNormalization_mul_symbol_eq_reduced
    (beta h : Real) (n : Nat) (k q : Real)
    (hx : 0 < beta * h / (2 * n))
    (hx1 : beta * h / (2 * n) < 1) :
    4 * Real.exp (-2 * quantumIsingVerticalCoupling beta h n) *
        triangularIsingSymbol (beta / (4 * n))
          (quantumIsingVerticalCoupling beta h n) 0 (k + Real.pi) q =
      2 * (1 - (beta * h / (2 * n)) ^ 2) *
        (quantumIsingTrotterReducedParameter beta h n k - Real.cos q) := by
  let x := beta * h / (2 * n)
  have hJ : 2 * quantumIsingVerticalCoupling beta h n = -Real.log x := by
    unfold quantumIsingVerticalCoupling
    dsimp only [x]
    ring
  have hexp : Real.exp (-2 * quantumIsingVerticalCoupling beta h n) = x := by
    rw [show -2 * quantumIsingVerticalCoupling beta h n =
      -(2 * quantumIsingVerticalCoupling beta h n) by ring,
      hJ, neg_neg, Real.exp_log hx]
  have hsinh : Real.sinh (2 * quantumIsingVerticalCoupling beta h n) =
      (1 - x ^ 2) / (2 * x) := by
    rw [hJ]
    exact quantumIsing_sinh_neg_log hx
  have hsinh0 : Real.sinh (2 * quantumIsingVerticalCoupling beta h n) ≠ 0 := by
    rw [hsinh]
    have hxSq : x ^ 2 < 1 := by nlinarith
    positivity
  have hreduced := triangularIsingTrotterSymbol_reduced beta h n k q hx hx1
  have hsymbol :
      triangularIsingSymbol (beta / (4 * n))
          (quantumIsingVerticalCoupling beta h n) 0 (k + Real.pi) q =
        Real.sinh (2 * quantumIsingVerticalCoupling beta h n) *
          (quantumIsingTrotterReducedParameter beta h n k - Real.cos q) := by
    simpa [mul_comm] using (div_eq_iff hsinh0).mp hreduced
  rw [hsymbol, hexp, hsinh]
  change 4 * x * ((1 - x ^ 2) / (2 * x) *
      (quantumIsingTrotterReducedParameter beta h n k - Real.cos q)) =
    2 * (1 - x ^ 2) *
      (quantumIsingTrotterReducedParameter beta h n k - Real.cos q)
  have hx0 : x ≠ 0 := hx.ne'
  field_simp [hx0] <;> ring


end StatMech.FrontierA
