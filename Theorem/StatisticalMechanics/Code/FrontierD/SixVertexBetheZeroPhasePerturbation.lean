/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhasePerturbation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddPhysicalExpansion
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhasePerturbation
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexBethePerturbRoot_same {n : Nat}
    (p : Fin n → Real) (ell : Fin n) (eps : Real) :
    sixVertexBethePerturbRoot p ell eps ell = eps := by
  simp [sixVertexBethePerturbRoot]

@[simp] theorem sixVertexBethePerturbRoot_ne {n : Nat}
    (p : Fin n → Real) (ell j : Fin n) (hj : j ≠ ell) (eps : Real) :
    sixVertexBethePerturbRoot p ell eps j = p j := by
  simp [sixVertexBethePerturbRoot, hj]

theorem sixVertexBethePerturbRoot_zero {n : Nat}
    (p : Fin n → Real) (ell : Fin n) (hell : p ell = 0) :
    sixVertexBethePerturbRoot p ell 0 = p := by
  funext j
  by_cases hj : j = ell
  · subst j
    simp [hell]
  · simp [sixVertexBethePerturbRoot, hj]

theorem continuous_sixVertexBethePerturbRoot {n : Nat}
    (p : Fin n → Real) (ell : Fin n) :
    Continuous (sixVertexBethePerturbRoot p ell) := by
  apply continuous_pi
  intro j
  by_cases hj : j = ell
  · subst j
    simpa using continuous_id
  · simpa [sixVertexBethePerturbRoot, hj] using
      (continuous_const : Continuous (fun _ : Real => p j))


theorem continuous_sixVertexBetheCollisionFreeIntervalSum_perturbRoot
    {n : Nat} (N : Nat) (c : Real) (p : Fin (n + 1) → Real)
    (ell : Fin (n + 1)) (x : Fin (n + 1) → Int) :
    Continuous (fun eps : Real =>
      sixVertexBetheCollisionFreeIntervalSum N c
        (fun i => sixVertexBethePhase
          (sixVertexBethePerturbRoot p ell eps i)) x) := by
  unfold sixVertexBetheCollisionFreeIntervalSum
    sixVertexBetheIntervalTupleWeight
  apply continuous_finsetSum
  intro q hq
  apply continuous_finsetProd
  intro i hi
  apply Continuous.mul continuous_const
  let f : Real → Complex := fun eps => sixVertexBethePhase
    (sixVertexBethePerturbRoot p ell eps i)
  have hf : Continuous f := by
    unfold f sixVertexBethePhase
    exact Complex.continuous_exp.comp
      (continuous_const.mul
        (Complex.continuous_ofReal.comp ((continuous_apply i).comp
          (continuous_sixVertexBethePerturbRoot p ell))))
  exact hf.zpow₀ (q i) (fun eps => Or.inl (Complex.exp_ne_zero _))


theorem sixVertexBetheCollisionFreeIntervalSum_perturbRoot_tendsto
    {n : Nat} (N : Nat) (c : Real) (p : Fin (n + 1) → Real)
    (ell : Fin (n + 1)) (hell : p ell = 0)
    (x : Fin (n + 1) → Int) :
    Tendsto (fun eps : Real =>
      sixVertexBetheCollisionFreeIntervalSum N c
        (fun i => sixVertexBethePhase
          (sixVertexBethePerturbRoot p ell eps i)) x)
      (nhdsWithin 0 {0}ᶜ)
      (nhds (sixVertexBetheCollisionFreeIntervalSum N c
        (fun i => sixVertexBethePhase (p i)) x)) := by
  let f : Real → Complex := fun eps =>
    sixVertexBetheCollisionFreeIntervalSum N c
      (fun i => sixVertexBethePhase
        (sixVertexBethePerturbRoot p ell eps i)) x
  have h : Tendsto f
      (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
      (nhds (f 0)) :=
    (continuous_sixVertexBetheCollisionFreeIntervalSum_perturbRoot
      N c p ell x).continuousAt.mono_left inf_le_left
  dsimp only [f] at h
  rw [sixVertexBethePerturbRoot_zero p ell hell] at h
  exact h

theorem sixVertexBethePerturbRoot_comp_perm {n : Nat}
    (p : Fin n → Real) (ell : Fin n) (eps : Real)
    (sigma : Equiv.Perm (Fin n)) (i : Fin n) :
    sixVertexBethePerturbRoot (fun j => p (sigma j)) (sigma.symm ell) eps i =
      sixVertexBethePerturbRoot p ell eps (sigma i) := by
  unfold sixVertexBethePerturbRoot
  by_cases hi : i = sigma.symm ell
  · subst i
    simp
  · have hsi : sigma i ≠ ell := by
      intro h
      exact hi (sigma.injective (h.trans (sigma.apply_symm_apply ell).symm))
    simp [hi, hsi]


theorem sixVertexBethePerturbRoot_eventually_phase_ne_one
    {n : Nat} (p : Fin n → Real) (ell : Fin n)
    (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
    ∀ᶠ eps in nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ,
      ∀ j, sixVertexBethePhase
        (sixVertexBethePerturbRoot p ell eps j) ≠ 1 := by
  have hinter : ∀ᶠ eps in nhdsWithin (0 : Real)
      (Set.singleton (0 : Real))ᶜ,
      eps ∈ Set.Ioo (-Real.pi) Real.pi := by
    exact mem_inf_of_left (Ioo_mem_nhds
      (neg_lt_zero.mpr Real.pi_pos) Real.pi_pos)
  have hne : ∀ᶠ eps in nhdsWithin (0 : Real)
      (Set.singleton (0 : Real))ᶜ, eps ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with eps heps
    simpa using heps
  filter_upwards [hinter, hne] with eps heps hneps j
  by_cases hj : j = ell
  · subst j
    simp only [sixVertexBethePerturbRoot_same]
    exact sixVertexBethePhase_ne_one_of_mem_Ioo_of_ne_zero heps hneps
  · rw [sixVertexBethePerturbRoot_ne p ell j hj]
    exact hother j hj


end
end StatMech.FrontierD
