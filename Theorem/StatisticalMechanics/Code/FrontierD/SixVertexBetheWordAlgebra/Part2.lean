/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAmplitudeExchange
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheWordAlgebra


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexBetheIntMonomial_rotate
    {N n : ℕ} (p : Fin (n + 1) → ℝ)
    (σ : Equiv.Perm (Fin (n + 1))) (x : Fin (n + 1) → ℤ) :
    sixVertexBetheIntMonomial p (σ * finRotate (n + 1)) x =
      sixVertexBethePhase (p (σ 0)) ^ N *
        sixVertexBetheIntMonomial p σ
          (sixVertexBetheShiftCoordinates N x) := by
  let z : Fin (n + 1) → ℂ := fun k => sixVertexBethePhase (p (σ k))
  have hz (k : Fin (n + 1)) : z k ≠ 0 := Complex.exp_ne_zero _
  have hrotate :
      (∏ k, z (finRotate (n + 1) k) ^ (x k)) =
        ∏ k, z k ^ (x ((finRotate (n + 1)).symm k)) := by
    simpa using (Equiv.prod_comp (finRotate (n + 1)).symm
      (fun k => z (finRotate (n + 1) k) ^ (x k))).symm
  unfold sixVertexBetheIntMonomial
  change (∏ k, z (finRotate (n + 1) k) ^ (x k)) = _
  rw [hrotate]
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [sixVertexBetheShiftCoordinates, Fin.cases_zero, Fin.cases_succ]
  have hr0 : (finRotate (n + 1)).symm 0 = Fin.last n := by
    rw [finRotate_symm_apply]
    apply Fin.ext
    simp
  have hrsucc (i : Fin n) :
      (finRotate (n + 1)).symm i.succ = i.castSucc := by
    rw [finRotate_symm_apply]
    apply Fin.ext
    simp [Fin.coe_sub_one]
  rw [hr0]
  simp_rw [hrsucc]
  have hpow : z 0 ^ (N : ℤ) * z 0 ^ (x (Fin.last n) - N) =
      z 0 ^ x (Fin.last n) := by
    rw [← zpow_add₀ (hz 0)]
    congr 1
    omega
  change z 0 ^ x (Fin.last n) * ∏ i : Fin n, z i.succ ^ x i.castSucc =
    z 0 ^ N * (z 0 ^ (x (Fin.last n) - N) *
      ∏ i : Fin n, z i.succ ^ x i.castSucc)
  rw [← zpow_natCast, ← mul_assoc, hpow]


theorem SixVertexSatisfiesMultiplicativeBetheEquations.changeVariables
    {c : ℝ} (hc : 2 < c) {N n : ℕ} {p : Fin (n + 1) → ℝ}
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
    (f : Equiv.Perm (Fin (n + 1)) → ℂ) (x : Fin (n + 1) → ℤ) :
    ∑ σ, sixVertexBetheAmplitude c p σ * f σ *
        sixVertexBetheIntMonomial p σ x =
      ∑ σ, sixVertexBetheAmplitude c p σ *
        f (σ * finRotate (n + 1)) *
          sixVertexBetheIntMonomial p σ
            (sixVertexBetheShiftCoordinates N x) := by
  let r : Equiv.Perm (Fin (n + 1)) := finRotate (n + 1)
  calc
    (∑ σ, sixVertexBetheAmplitude c p σ * f σ *
        sixVertexBetheIntMonomial p σ x) =
      ∑ σ, sixVertexBetheAmplitude c p (σ * r) * f (σ * r) *
        sixVertexBetheIntMonomial p (σ * r) x := by
      simpa [r] using
        (Equiv.sum_comp (Equiv.mulRight r)
          (fun σ => sixVertexBetheAmplitude c p σ * f σ *
            sixVertexBetheIntMonomial p σ x)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [sixVertexBetheIntMonomial_rotate (N := N)]
      calc
        _ = (sixVertexBethePhase (p (σ 0)) ^ N *
              sixVertexBetheAmplitude c p (σ * r)) *
            f (σ * r) * sixVertexBetheIntMonomial p σ
              (sixVertexBetheShiftCoordinates N x) := by ring
        _ = _ := by rw [show r = finRotate (n + 1) by rfl,
          hp.amplitude_rotate hc]


end
end StatMech.FrontierD
