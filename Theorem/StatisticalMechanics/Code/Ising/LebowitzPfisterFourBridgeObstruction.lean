/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterThreeBridgeClosure
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterStrongMarkedSite
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeObstruction


namespace StatMech.Ising

noncomputable section

theorem hasDerivAt_fourBridgeTiltMean_tanh
    (r a b c d : Real)
    (hP : 1 + a * Real.tanh r + b * Real.tanh r ^ 2 +
      c * Real.tanh r ^ 3 + d * Real.tanh r ^ 4 ≠ 0) :
    HasDerivAt (fun u => fourBridgeTiltMean (Real.tanh u) a b c d)
      (fourBridgeTiltVariance (Real.tanh r) a b c d) r := by
  let t := Real.tanh r
  let U : Real -> Real := fun u => 1 - u ^ 2
  let Q : Real -> Real := fun u =>
    a + 2 * b * u + 3 * c * u ^ 2 + 4 * d * u ^ 3
  let P : Real -> Real := fun u =>
    1 + a * u + b * u ^ 2 + c * u ^ 3 + d * u ^ 4
  have hU : HasDerivAt U (-2 * t) t := by
    dsimp [U]
    convert (hasDerivAt_const t 1).sub ((hasDerivAt_id t).pow 2) using 1 <;>
      simp [id_eq] <;> ring
  have hQ : HasDerivAt Q
      (2 * b + 6 * c * t + 12 * d * t ^ 2) t := by
    dsimp [Q]
    convert (((hasDerivAt_const t a).add
      ((hasDerivAt_id t).const_mul (2 * b))).add
      (((hasDerivAt_id t).pow 2).const_mul (3 * c))).add
      (((hasDerivAt_id t).pow 3).const_mul (4 * d)) using 1 <;>
      simp [id_eq] <;> ring
  have hPderiv : HasDerivAt P
      (a + 2 * b * t + 3 * c * t ^ 2 + 4 * d * t ^ 3) t := by
    dsimp [P]
    convert ((((hasDerivAt_const t 1).add
      ((hasDerivAt_id t).const_mul a)).add
      (((hasDerivAt_id t).pow 2).const_mul b)).add
      (((hasDerivAt_id t).pow 3).const_mul c)).add
      (((hasDerivAt_id t).pow 4).const_mul d) using 1 <;>
      simp [id_eq] <;> ring
  have hP' : P t ≠ 0 := by simpa [P, t] using hP
  have houter := ((hasDerivAt_id t).const_mul 4).add
    ((hU.mul hQ).div hPderiv hP')
  have htderiv : HasDerivAt Real.tanh (1 - t ^ 2) r := by
    have h := hasDerivAt_tanh r
    convert h using 1
    dsimp [t]
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [(Real.cosh_pos r).ne']
    nlinarith [Real.cosh_sq_sub_sinh_sq r]
  have hcomp := houter.comp r htderiv
  change HasDerivAt
    (fun u => 4 * Real.tanh u +
      U (Real.tanh u) * Q (Real.tanh u) / P (Real.tanh u)) _ r at hcomp
  convert hcomp using 1
  change fourBridgeTiltVariance t a b c d = _
  let den := 1 + a * t + b * t ^ 2 + c * t ^ 3 + d * t ^ 4
  let q := a + 2 * b * t + 3 * c * t ^ 2 + 4 * d * t ^ 3
  let qp := 2 * b + 6 * c * t + 12 * d * t ^ 2
  have hden : den ≠ 0 := by simpa [den, t] using hP
  dsimp [U, Q, P, fourBridgeTiltVariance]
  simp only [mul_one]
  change
    (t - 1) * (t + 1) *
        (-3 * a ^ 2 * t ^ 2 + a ^ 2 - 4 * a * b * t ^ 3 +
          2 * a * b * t + 6 * a * d * t ^ 5 - 4 * a * d * t ^ 3 -
          6 * a * t - 2 * b ^ 2 * t ^ 4 + 2 * b ^ 2 * t ^ 2 -
          2 * b * c * t ^ 5 + 4 * b * c * t ^ 3 +
          2 * b * d * t ^ 6 + 2 * b * d * t ^ 4 - 2 * b * t ^ 2 -
          2 * b - c ^ 2 * t ^ 6 + 3 * c ^ 2 * t ^ 4 +
          6 * c * d * t ^ 5 + 4 * c * t ^ 3 - 6 * c * t +
          4 * d ^ 2 * t ^ 6 + 12 * d * t ^ 4 - 12 * d * t ^ 2 - 4) /
        den ^ 2 =
      (4 + (((-2 * t) * q + (1 - t ^ 2) * qp) * den -
        (1 - t ^ 2) * q * q) / den ^ 2) * (1 - t ^ 2)
  field_simp [hden]
  ring


end
end StatMech.Ising
