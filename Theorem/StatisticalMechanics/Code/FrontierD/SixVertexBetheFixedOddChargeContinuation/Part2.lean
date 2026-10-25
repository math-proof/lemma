/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedOddChargeContinuation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricCovering
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeContinuationPoint
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedOddChargeContinuation
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFixedOddChargeBetheRoots_mem_open
    {c : Real} (hc : 2 < c) (s k : Nat) :
    SixVertexOpenRootSimplex (sixVertexFixedOddChargeBetheRoots hc s k) := by
  let e : Fin (((s + k + 1) + 1) + (s + k + 1)) ≃
      Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) :=
    (Fin.castOrderIso
      (sixVertexFixedOddChargeBetheParticleCount_eq s k).symm).toEquiv
  have h := sixVertexFixedChargeBetheRoots_mem_open hc (2 * s + 1) k
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    exact h.1 (by simpa [e] using hij)
  · intro i
    have hs := h.2.1 (e i)
    have hrev : e i.rev = (e i).rev := by
      apply Fin.ext
      simp [e, Fin.rev]
      omega
    unfold sixVertexFixedOddChargeBetheRoots
    change sixVertexFixedChargeBetheRoots hc (2 * s + 1) k (e i.rev) = _
    rw [hrev]
    exact hs
  · intro i
    exact h.2.2 (e i)

theorem sixVertexFixedOddChargeBetheRoots_is_solution
    {c : Real} (hc : 2 < c) (s k : Nat) :
    SixVertexSatisfiesBetheEquations c (sixVertexFourWidth (2 * s + 1) k)
      (((s + k + 1) + 1) + (s + k + 1))
      (sixVertexFixedOddChargeBetheRoots hc s k) := by
  let e : Fin (((s + k + 1) + 1) + (s + k + 1)) ≃
      Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) :=
    (Fin.castOrderIso
      (sixVertexFixedOddChargeBetheParticleCount_eq s k).symm).toEquiv
  intro j
  have hj := sixVertexFixedChargeBetheRoots_is_solution hc (2 * s + 1) k (e j)
  have hquantum : sixVertexCentralQuantumNumber (e j) =
      sixVertexCentralQuantumNumber j := by
    rw [sixVertexCentralQuantumNumber_eq, sixVertexCentralQuantumNumber_eq]
    simp [e]
    ring
  let f : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) → Real :=
    fun l => sixVertexTheta c
      (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k (e j))
      (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k l)
  have hsum : (∑ l, f l) = ∑ l, f (e l) := by
    simpa using (Equiv.sum_comp e f).symm
  rw [hquantum] at hj
  rw [show (∑ l, sixVertexTheta c
      (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k (e j))
      (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k l)) =
        ∑ l, f l by rfl, hsum] at hj
  simpa [sixVertexFixedOddChargeBetheRoots, e, f] using hj

end
end StatMech.FrontierD
