/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTorusLocalLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusFreeBoundaryMonomialComparison.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityCriticalAxisClosure
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit.Part6
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part11
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPhaseEndpoint
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalTorusLocalLimit
open Filter Finset MeasureTheory Set Topology


namespace StatMech.FrontierA

open StatMech Ising Lattice Sharpness StatMech.FrontierB

noncomputable section

theorem boxFinsetSpinSupport_map_subtype
    {d n : Nat} (A : Finset (Site d))
    (hA : (↑A : Set (Site d)) ⊆ box d n) :
    (boxFinsetSpinSupport d n A).map
        (Function.Embedding.subtype fun x ↦ x ∈ boxFinset d n) = A := by
  ext x
  simp only [Finset.mem_map, boxFinsetSpinSupport, Finset.mem_filter,
    Finset.mem_univ, true_and, Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, mem_boxFinset.mpr (hA hx)⟩, hx, rfl⟩

theorem boxSpinSupport_map_iptp_boxEquiv
    {d n : Nat} (A : Finset (Site d)) :
    (boxSpinSupport d n A).map (iptp_boxEquiv d n).toEmbedding =
      boxFinsetSpinSupport d n A := by
  ext x
  simp [boxSpinSupport, boxFinsetSpinSupport, iptp_boxEquiv]
  change ((iptp_boxEquiv d n).symm x).1 ∈ A ↔ x.1 ∈ A
  rfl


theorem isingExpectation_boxFinsetSpinSupport_eq_freeMeasure
    {d n : Nat} (beta : Real) (A : Finset (Site d))
    (hA : (↑A : Set (Site d)) ⊆ box d n) :
    isingExpectation (graphS d (boxFinset d n)) beta 0
        (spinProd (boxFinsetSpinSupport d n A)) =
      ∫ omega, spinProd A omega
        ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d))) := by
  have hadj : ∀ x y : sctBox d n,
      (sctBoxGraph d n).Adj x y ↔
        (graphS d (boxFinset d n)).Adj
          (iptp_boxEquiv d n x) (iptp_boxEquiv d n y) := by
    intro x y
    rfl
  have hrel := isingExpectation_spinProd_relabel
    (sctBoxGraph d n) (graphS d (boxFinset d n))
    (iptp_boxEquiv d n) hadj beta 0 (boxSpinSupport d n A)
  rw [boxSpinSupport_map_iptp_boxEquiv] at hrel
  rw [integral_freeMeasure_spinProd d n beta 0 A hA]
  exact hrel.symm

theorem two_mul_succ_lt_isingDyadicSide (n : Nat) :
    2 * (n + 1) < isingDyadicSide n := by
  unfold isingDyadicSide
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by omega, pow_succ]
      have hp : 1 ≤ 2 ^ (n + 2) := one_le_pow₀ (by norm_num)
      omega


theorem criticalFreeState_eq_plusState {d : Nat} (hd : 2 < d) :
    (freeState d (IsingFK.betaC (magnetization d)) 0 :
        Measure (ConfigSpace (Site d))) =
      (plusState d (IsingFK.betaC (magnetization d)) 0 :
        Measure (ConfigSpace (Site d))) := by
  have hbeta : 0 ≤ IsingFK.betaC (magnetization d) := by
    rw [isingFK_betaC_eq_tildeBetaCIsing (by omega : 2 ≤ d)]
    exact (tildeBetaCIsing_pos (by omega : 2 ≤ d)).le
  exact StatMech.Onsager.freeState_eq_plusState_of_magnetization_eq_zero
    (IsingFK.betaC (magnetization d)) hbeta
    (isingCritical_magnetization_zero_and_gibbs_unique hd).1


end
end StatMech.FrontierA
