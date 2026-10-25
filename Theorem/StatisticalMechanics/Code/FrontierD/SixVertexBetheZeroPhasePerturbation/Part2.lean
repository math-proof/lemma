/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhasePerturbation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddPhysicalExpansion
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhasePerturbation.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem continuous_sixVertexBethePerturbedIntervalTotal
    {n : Nat} (N : Nat) (c : Real) (p : Fin (n + 1) → Real)
    (ell : Fin (n + 1)) (x : Fin (n + 1) → Int) :
    Continuous (sixVertexBethePerturbedIntervalTotal N c p ell x) := by
  unfold sixVertexBethePerturbedIntervalTotal
  apply continuous_finsetSum
  intro sigma hsigma
  apply Continuous.mul continuous_const
  let q : Fin (n + 1) → Real := fun i => p (sigma i)
  let a : Fin (n + 1) := sigma.symm ell
  have h := continuous_sixVertexBetheCollisionFreeIntervalSum_perturbRoot
    N c q a x
  convert h using 1
  funext eps
  congr 2
  funext i
  rw [sixVertexBethePerturbRoot_comp_perm]


theorem SixVertexSatisfiesMultiplicativeBetheEquations.perturbedIntervalTotal_tendsto_physicalAction
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 1) → Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
    (ell : Fin (n + 1)) (hell : p ell = 0)
    (x : SixVertexSector N (n + 1)) :
    Tendsto (sixVertexBethePerturbedIntervalTotal N c p ell
        (sixVertexSectorIntCoordinates x))
      (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
      (nhds ((sixVertexSectorTransferComplex N (n + 1) c).mulVec
        (sixVertexCoordinateBetheWave c p) x)) := by
  let F := sixVertexBethePerturbedIntervalTotal N c p ell
    (sixVertexSectorIntCoordinates x)
  have hcont : Tendsto F
      (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
      (nhds (F 0)) :=
    (continuous_sixVertexBethePerturbedIntervalTotal N c p ell
      (sixVertexSectorIntCoordinates x)).continuousAt.mono_left inf_le_left
  have hzero : F 0 =
      (sixVertexSectorTransferComplex N (n + 1) c).mulVec
        (sixVertexCoordinateBetheWave c p) x := by
    dsimp only [F, sixVertexBethePerturbedIntervalTotal]
    simp_rw [sixVertexBethePerturbRoot_zero p ell hell]
    rw [hp.physicalZeroPhaseIntervalExpansion hc p ell hell x]
    apply Finset.sum_congr rfl
    intro sigma hsigma
    congr 1
    rw [sixVertexBetheCollisionFreeIntervalSum_zeroPhase N c
      (fun i => p (sigma i)) (sixVertexSectorIntCoordinates x)
      (sigma.symm ell)]
    · simp [hell]
    · exact sixVertexBetheShiftCoordinates_lt_sector x
  rwa [hzero] at hcont


theorem sixVertexBethePerturbedIntervalTotal_eventuallyEq_wordTotal
    {n : Nat} (N : Nat) (c : Real) (p : Fin (n + 1) → Real)
    (ell : Fin (n + 1)) (hell : p ell = 0)
    (hopen : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
    (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1)
    (x : Fin (n + 1) → Int) (hgap : ∀ i,
      sixVertexBetheShiftCoordinates N x i < x i) :
    sixVertexBethePerturbedIntervalTotal N c p ell x =ᶠ[nhdsWithin
      (0 : Real) (Set.singleton (0 : Real))ᶜ]
      sixVertexBethePerturbedWordTotal N c p ell x := by
  filter_upwards [sixVertexBethePerturbRoot_eventually_phase_ne_one
    p ell hother] with eps hphase
  unfold sixVertexBethePerturbedIntervalTotal
    sixVertexBethePerturbedWordTotal
  apply Finset.sum_congr rfl
  intro sigma hsigma
  congr 1
  let z : Fin (n + 1) → Complex := fun j => sixVertexBethePhase
    (sixVertexBethePerturbRoot p ell eps j)
  rw [sixVertexBetheCollisionFreeIntervalSum_eq_words N c
    (fun i => z (sigma i)) x hgap
    (fun i => Complex.exp_ne_zero _) (fun i => hphase (sigma i))]
  apply Finset.sum_congr rfl
  intro w hw
  have hcoeff :
      sixVertexBetheWordCoefficient c (fun i => z (sigma i))
          (Equiv.refl _) w =
        sixVertexBetheWordCoefficient c z sigma w := by
    unfold sixVertexBetheWordCoefficient
    apply Finset.prod_congr rfl
    intro i hi
    simp [sixVertexBetheWordEdgeFactor]
  have hmono :
      sixVertexBetheWordMonomial N (fun i => z (sigma i))
          (Equiv.refl _) x w =
        sixVertexBetheWordMonomial N z sigma x w := by
    unfold sixVertexBetheWordMonomial
    apply Finset.prod_congr rfl
    intro i hi
    simp
  rw [hcoeff, hmono]


theorem SixVertexSatisfiesMultiplicativeBetheEquations.perturbedWordTotal_tendsto_physicalAction
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 1) → Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
    (ell : Fin (n + 1)) (hell : p ell = 0)
    (hopen : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
    (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1)
    (x : SixVertexSector N (n + 1)) :
    Tendsto (sixVertexBethePerturbedWordTotal N c p ell
        (sixVertexSectorIntCoordinates x))
      (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
      (nhds ((sixVertexSectorTransferComplex N (n + 1) c).mulVec
        (sixVertexCoordinateBetheWave c p) x)) := by
  apply (hp.perturbedIntervalTotal_tendsto_physicalAction
    hc p ell hell x).congr'
  exact (sixVertexBethePerturbedIntervalTotal_eventuallyEq_wordTotal
    N c p ell hell hopen hother (sixVertexSectorIntCoordinates x)
    (sixVertexBetheShiftCoordinates_lt_sector x))

end
end StatMech.FrontierD
