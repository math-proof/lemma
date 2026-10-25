/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedSelectedLaws.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPhaseTransport.Part3
import Theorem.StatisticalMechanics.Code.FK.PlacementClose.Part2
open MeasureTheory Set Filter Topology
open scoped BigOperators Classical


namespace StatMech

namespace OSSS

namespace FKSharpnessWeightedSelectedLaws

open Lattice FK Percolation

open RevealmentConstruction WiredBoxDifferential WiredBoxLocalized WiredBoxOffCentre

open FKSharpnessWeightedPeriodic

open FKSharpnessWeightedInfiniteVolume

open FKSharpnessWeightedCoherentLimit

open FKSharpnessWeightedPhaseTransport

variable {d : Nat}


theorem closedFiber_pairMass_eq_sum
    {E : Type*} [Fintype E] [DecidableEq E]
    (m : ConfigSpace E -> Real) (e : E) :
    (∑ psi ∈ Finset.univ.filter
        (fun psi : ConfigSpace E => psi e = false),
      (m (setOpen e psi) + m (setClosed e psi))) =
      ∑ omega, m omega := by
  rw [Finset.sum_add_distrib, <- openMarginal_eq_closedFiber]
  have hclosed :
      (∑ psi ∈ Finset.univ.filter
          (fun psi : ConfigSpace E => psi e = false),
        m (setClosed e psi)) =
        ∑ omega ∈ Finset.univ.filter
          (fun omega : ConfigSpace E => omega e = false), m omega := by
    apply Finset.sum_congr rfl
    intro psi hpsi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpsi
    congr 1
    funext x
    by_cases hx : x = e
    · subst x
      simp [hpsi]
    · simp [setClosed_of_ne hx]
  rw [hclosed]
  unfold openMarginal
  rw [show Finset.univ.filter (fun omega : ConfigSpace E => omega e = false) =
      Finset.univ.filter (fun omega : ConfigSpace E => ¬ omega e = true) by
        ext omega
        simp]
  rw [Finset.sum_filter_add_sum_filter_not]

theorem finite_singleOpen_preimage_bound
    {E : Type*} [Fintype E] [DecidableEq E]
    (mu : ConfigSpace E -> Real) (e : E) (c : Real)
    (hmu : forall omega, 0 <= mu omega)
    (hpair : forall psi,
      c * (mu (setOpen e psi) + mu (setClosed e psi)) <=
        mu (setOpen e psi))
    (A : Set (ConfigSpace E)) :
    c * (∑ omega,
        (setOpen e ⁻¹' A).indicator (fun _ => (1 : Real)) omega * mu omega) <=
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega * mu omega := by
  let S := Finset.univ.filter (fun psi : ConfigSpace E => psi e = false)
  have hlhs := closedFiber_pairMass_eq_sum
    (fun omega => (setOpen e ⁻¹' A).indicator (fun _ => (1 : Real)) omega * mu omega) e
  have hrhs := closedFiber_pairMass_eq_sum
    (fun omega => A.indicator (fun _ => (1 : Real)) omega * mu omega) e
  rw [<- hlhs, <- hrhs, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro psi hpsi
  have hopenopen : setOpen e (setOpen e psi) = setOpen e psi := by
    funext x
    by_cases hx : x = e
    · subst x
      simp
    · simp [setOpen_of_ne hx]
  have hopenclosed : setOpen e (setClosed e psi) = setOpen e psi := by
    funext x
    by_cases hx : x = e
    · subst x
      simp
    · simp [setOpen_of_ne hx, setClosed_of_ne hx]
  have hpreopen : setOpen e psi ∈ setOpen e ⁻¹' A ↔ setOpen e psi ∈ A := by
    change setOpen e (setOpen e psi) ∈ A ↔ _
    rw [hopenopen]
  have hpreclosed : setClosed e psi ∈ setOpen e ⁻¹' A ↔ setOpen e psi ∈ A := by
    change setOpen e (setClosed e psi) ∈ A ↔ _
    rw [hopenclosed]
  by_cases hAopen : setOpen e psi ∈ A
  · rw [Set.indicator_of_mem (hpreopen.mpr hAopen),
      Set.indicator_of_mem (hpreclosed.mpr hAopen),
      Set.indicator_of_mem hAopen]
    by_cases hAclosed : setClosed e psi ∈ A
    · rw [Set.indicator_of_mem hAclosed]
      simpa only [one_mul] using (hpair psi).trans
        (le_add_of_nonneg_right (hmu (setClosed e psi)))
    · rw [Set.indicator_of_notMem hAclosed, zero_mul, add_zero]
      simpa only [one_mul] using hpair psi
  · rw [Set.indicator_of_notMem (not_congr hpreopen |>.mpr hAopen),
      Set.indicator_of_notMem (not_congr hpreclosed |>.mpr hAopen),
      Set.indicator_of_notMem hAopen, zero_mul, zero_mul, add_zero]
    by_cases hAclosed : setClosed e psi ∈ A
    · rw [Set.indicator_of_mem hAclosed]
      simpa only [one_mul, zero_mul, mul_zero, zero_add] using hmu (setClosed e psi)
    · rw [Set.indicator_of_notMem hAclosed, zero_mul, add_zero]
      simp


end FKSharpnessWeightedSelectedLaws
end OSSS
end StatMech
