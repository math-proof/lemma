/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedEvenChargePerronClosed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeContinuationPoint
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexSectorTopEigenvalue_eq_of_count_eq
    {N n q : Nat} (h : n = q) (hn : n ≤ N) (hq : q ≤ N) (c : Real) :
    sixVertexSectorTopEigenvalue N n hn c =
      sixVertexSectorTopEigenvalue N q hq c := by
  subst q
  rfl

theorem sixVertexCoordinateBetheWave_cast_ne_zero
    {N n q : Nat} {c : Real} (h : n = q) (p : Fin n → Real)
    (hp : sixVertexCoordinateBetheWave (N := N) c p ≠ 0) :
    sixVertexCoordinateBetheWave (N := N) c
      (fun i : Fin q => p (Fin.cast h.symm i)) ≠ 0 := by
  subst q
  simpa using hp

theorem sixVertexFixedEvenChargeBetheRoots_mem_open
    {c : Real} (hc : 2 < c) (s k : Nat) :
    SixVertexOpenRootSimplex (sixVertexFixedEvenChargeBetheRoots hc s k) := by
  let e : Fin ((s + k + 1) + (s + k + 1)) ≃
      Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k) :=
    (Fin.castOrderIso
      (sixVertexFixedEvenChargeBetheParticleCount_eq s k).symm).toEquiv
  have h := sixVertexFixedChargeBetheRoots_mem_open hc (2 * s) k
  refine ⟨?_, sixVertexFixedEvenChargeBetheRoots_symmetric hc s k, ?_⟩
  · intro i j hij
    exact h.1 (by simpa [e] using hij)
  · intro i
    exact h.2.2 (e i)

theorem sixVertexFixedEvenChargeBetheRoots_is_solution
    {c : Real} (hc : 2 < c) (s k : Nat) :
    SixVertexSatisfiesBetheEquations c (sixVertexFourWidth (2 * s) k)
      ((s + k + 1) + (s + k + 1))
      (sixVertexFixedEvenChargeBetheRoots hc s k) := by
  let e : Fin ((s + k + 1) + (s + k + 1)) ≃
      Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k) :=
    (Fin.castOrderIso
      (sixVertexFixedEvenChargeBetheParticleCount_eq s k).symm).toEquiv
  intro j
  have hj := sixVertexFixedChargeBetheRoots_is_solution hc (2 * s) k (e j)
  have hquantum : sixVertexCentralQuantumNumber (e j) =
      sixVertexCentralQuantumNumber j := by
    rw [sixVertexCentralQuantumNumber_eq, sixVertexCentralQuantumNumber_eq]
    simp [e]
    ring
  let f : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k) → Real :=
    fun l => sixVertexTheta c
      (sixVertexFixedChargeBetheRoots hc (2 * s) k (e j))
      (sixVertexFixedChargeBetheRoots hc (2 * s) k l)
  have hsum : (∑ l, f l) = ∑ l, f (e l) := by
    simpa using (Equiv.sum_comp e f).symm
  rw [hquantum] at hj
  rw [show (∑ l, sixVertexTheta c
      (sixVertexFixedChargeBetheRoots hc (2 * s) k (e j))
      (sixVertexFixedChargeBetheRoots hc (2 * s) k l)) =
        ∑ l, f l by rfl, hsum] at hj
  simpa [sixVertexFixedEvenChargeBetheRoots, e, f] using hj

theorem sixVertexFixedEvenPositiveBetheRoots_mem_Ioo
    {c : Real} (hc : 2 < c) (s k : Nat) (j : Fin (s + k + 1)) :
    sixVertexFixedEvenPositiveBetheRoots hc s k j ∈ Set.Ioo 0 Real.pi := by
  let m := s + k + 1
  let p := sixVertexFixedEvenChargeBetheRoots hc s k
  let i : Fin (m + m) := Fin.natAdd m j
  let ir : Fin (m + m) := Fin.castAdd m j.rev
  have hopen := sixVertexFixedEvenChargeBetheRoots_mem_open hc s k
  have hir : ir < i := by
    rw [Fin.lt_def]
    simp [ir, i, Fin.castAdd, m]
    omega
  have hneg : p ir = -p i := by
    have hs := (sixVertexFixedEvenChargeBetheRoots_symmetric hc s k) i
    have hrev : i.rev = ir := by
      apply Fin.ext
      simp [i, ir, Fin.rev, Fin.castAdd, m]
      omega
    simpa [hrev] using hs
  have hpos : 0 < p i := by
    have hlt := hopen.1 hir
    change p ir < p i at hlt
    rw [hneg] at hlt
    linarith
  exact ⟨hpos, hopen.2.2 i |>.2⟩


end
end StatMech.FrontierD
