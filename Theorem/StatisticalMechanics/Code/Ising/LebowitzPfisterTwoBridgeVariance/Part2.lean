/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoBridgeVariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterSingleBridgeVariance.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterTwoBridgeVariance.Part2


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem replicaBridgeMean_twoBridgeSites_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (x y : V) (r : Real) :
    replicaBridgeMean G J hf (twoBridgeSites x y) r =
      twoBridgeTiltMean (Real.tanh r)
        ((expJ G.edgeFinset J hf (fun s => spin s x)) ^ 2 +
          (expJ G.edgeFinset J hf (fun s => spin s y)) ^ 2)
        ((expJ G.edgeFinset J hf
          (fun s => spin s x * spin s y)) ^ 2) := by
  let mx := expJ G.edgeFinset J hf (fun s => spin s x)
  let my := expJ G.edgeFinset J hf (fun s => spin s y)
  let cxy := expJ G.edgeFinset J hf (fun s => spin s x * spin s y)
  let A := mx ^ 2 + my ^ 2
  let E := cxy ^ 2
  let M : Real -> Real := fun u =>
    Real.cosh u ^ 2 + Real.cosh u * Real.sinh u * A +
      Real.sinh u ^ 2 * E
  have hmoment (u : Real) :
      replicaBridgeMoment G J hf (twoBridgeSites x y) u = M u := by
    rw [replicaBridgeMoment_twoBridgeSites_eq,
      twoReplicaTwoBridgeMoment_eq]
  have hMderiv : HasDerivAt M
      (2 * Real.cosh r * Real.sinh r +
        (Real.cosh r ^ 2 + Real.sinh r ^ 2) * A +
        2 * Real.sinh r * Real.cosh r * E) r := by
    dsimp [M]
    convert ((Real.hasDerivAt_cosh r).pow 2).add
      (((Real.hasDerivAt_cosh r).mul (Real.hasDerivAt_sinh r)).mul_const A) |>.add
      (((Real.hasDerivAt_sinh r).pow 2).mul_const E) using 1 <;> ring
  have hMpos : 0 < M r := by
    rw [← hmoment]
    exact replicaBridgeMoment_pos G J hf (twoBridgeSites x y) r
  have hlogM := hMderiv.log hMpos.ne'
  have hlogBridge :=
    hasDerivAt_log_replicaBridgeMoment G J hf (twoBridgeSites x y) r
  have hfun :
      (fun u => Real.log
        (replicaBridgeMoment G J hf (twoBridgeSites x y) u)) =
      (fun u => Real.log (M u)) := by
    funext u
    rw [hmoment]
  rw [hfun] at hlogBridge
  have hmean : replicaBridgeMean G J hf (twoBridgeSites x y) r =
      (2 * Real.cosh r * Real.sinh r +
        (Real.cosh r ^ 2 + Real.sinh r ^ 2) * A +
        2 * Real.sinh r * Real.cosh r * E) / M r :=
    hlogBridge.unique hlogM
  rw [hmean]
  change _ = twoBridgeTiltMean (Real.tanh r) A E
  have hD : Real.cosh r ^ 2 + Real.cosh r * Real.sinh r * A +
      Real.sinh r ^ 2 * E ≠ 0 := by
    simpa [M] using hMpos.ne'
  have hD' : Real.cosh r * Real.sinh r * A + Real.cosh r ^ 2 +
      Real.sinh r ^ 2 * E ≠ 0 := by
    simpa [add_comm, add_left_comm, add_assoc] using hD
  unfold twoBridgeTiltMean M
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc : Real.cosh r ≠ 0 := (Real.cosh_pos r).ne'
  have hcs : Real.cosh r ^ 2 = Real.sinh r ^ 2 + 1 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq r]
  have hPidentity :
      1 + A * (Real.sinh r / Real.cosh r) +
          E * (Real.sinh r / Real.cosh r) ^ 2 =
        (Real.cosh r ^ 2 + Real.cosh r * Real.sinh r * A +
          Real.sinh r ^ 2 * E) / Real.cosh r ^ 2 := by
    field_simp [hc]
  rw [hPidentity]
  have hDc :
      (Real.cosh r ^ 2 + Real.cosh r * Real.sinh r * A +
          Real.sinh r ^ 2 * E) / Real.cosh r ^ 2 ≠ 0 :=
    div_ne_zero hD (pow_ne_zero 2 hc)
  rw [show
    (1 - (Real.sinh r / Real.cosh r) ^ 2) *
          (A + 2 * E * (Real.sinh r / Real.cosh r)) /
        ((Real.cosh r ^ 2 + Real.cosh r * Real.sinh r * A +
          Real.sinh r ^ 2 * E) / Real.cosh r ^ 2) =
      (1 - (Real.sinh r / Real.cosh r) ^ 2) *
          (A + 2 * E * (Real.sinh r / Real.cosh r)) *
        Real.cosh r ^ 2 /
          (Real.cosh r ^ 2 + Real.cosh r * Real.sinh r * A +
            Real.sinh r ^ 2 * E) by
      field_simp [hc, hD, hDc]]
  apply (div_eq_iff hD).2
  rw [add_mul
    (2 * (Real.sinh r / Real.cosh r))
    ((1 - (Real.sinh r / Real.cosh r) ^ 2) *
      (A + 2 * E * (Real.sinh r / Real.cosh r)) * Real.cosh r ^ 2 /
        (Real.cosh r ^ 2 + Real.cosh r * Real.sinh r * A +
          Real.sinh r ^ 2 * E))
    (Real.cosh r ^ 2 + Real.cosh r * Real.sinh r * A +
      Real.sinh r ^ 2 * E)]
  rw [div_mul_cancel₀ _ hD]
  field_simp [hc]
  have hcsE := congrArg
    (fun z : Real => z * Real.sinh r * E * 2) hcs
  ring_nf at hcsE ⊢


end
end StatMech.Ising
