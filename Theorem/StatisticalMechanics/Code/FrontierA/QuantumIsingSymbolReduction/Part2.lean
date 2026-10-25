/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSymbolReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterLocal.Part2
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingSymbolReduction


namespace StatMech.FrontierA

theorem triangularIsingTrotterSymbol_reduced
    (beta h : Real) (n : Nat) (k q : Real)
    (hx : 0 < beta * h / (2 * n)) (hx1 : beta * h / (2 * n) < 1) :
    triangularIsingSymbol (beta / (4 * n))
        (quantumIsingVerticalCoupling beta h n) 0 (k + Real.pi) q /
        Real.sinh (2 * quantumIsingVerticalCoupling beta h n) =
      quantumIsingTrotterReducedParameter beta h n k - Real.cos q := by
  let x := beta * h / (2 * n)
  have hJ : 2 * quantumIsingVerticalCoupling beta h n = -Real.log x := by
    unfold quantumIsingVerticalCoupling
    dsimp [x]
    ring
  have hsinh : Real.sinh (-Real.log x) ≠ 0 := by
    rw [sinh_neg_log_eq hx]
    have hden : 1 - x ^ 2 ≠ 0 := by nlinarith
    positivity
  unfold triangularIsingSymbol quantumIsingTrotterReducedParameter
  simp only [Real.cosh_zero, Real.sinh_zero, mul_one, mul_zero, add_zero,
    Real.cos_add_pi]
  rw [show 2 * (beta / (4 * (n : Real))) = beta / (2 * n) by ring, hJ]
  simpa [x] using reduced_symbol_algebra
    (beta / (2 * (n : Real))) x k q hx hx1

end StatMech.FrontierA
