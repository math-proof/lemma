/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
import Theorem.StatisticalMechanics.Code.Lattice.LeftFace.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceOrbit.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ExitDartsOrbit
import Theorem.StatisticalMechanics.Code.Lattice.JordanSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Percolation.OutermostContour.Part2
import Theorem.StatisticalMechanics.Code.Percolation.PcFarContour
import Def.StatisticalMechanics.Code.Percolation.FarDartContour.Part4
open Finset Set SimpleGraph Function


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {ω : ConfigSpace (Sym2 (Site 2))}


@[simp] theorem fdc_farLeftExitDart_tail (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ) :
    (fdc_farLeftExitDart (ω := ω) hfin R).tail
      = leftAxisSite (fdc_leftExitIdx (ω := ω) hfin R) := rfl

@[simp] theorem fdc_farLeftExitDart_head (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ) :
    (fdc_farLeftExitDart (ω := ω) hfin R).head
      = leftAxisSite (fdc_leftExitIdx (ω := ω) hfin R + 1) := rfl


theorem fdc_farLeftExitDart_isBoundaryDart (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ)
    (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
    IsBoundaryDart (cluster 2 ω (origin 2)) (fdc_farLeftExitDart (ω := ω) hfin R) :=
  ⟨fdc_leftExitIdx_mem (ω := ω) hfin R, fdc_leftExitIdx_succ_not_mem (ω := ω) hfin R hR⟩


theorem fdc_leftAxis_reach (K : Set (Site 2)) (a j : ℕ)
    (hout : ∀ k, a ≤ k → k ≤ a + j → (leftAxisSite k : Site 2) ∉ K) :
    ((hypercubicLattice 2).induce Kᶜ).Reachable
      ⟨leftAxisSite a, hout a le_rfl (by omega)⟩
      ⟨leftAxisSite (a + j), hout (a + j) (by omega) le_rfl⟩ := by
  induction j with
  | zero => exact Reachable.refl _
  | succ n ih =>
    have hout' : ∀ k, a ≤ k → k ≤ a + n → (leftAxisSite k : Site 2) ∉ K := by
      intro k h1 h2; exact hout k h1 (by omega)
    have h1 := ih hout'
    have hk1 : (leftAxisSite (a + n) : Site 2) ∉ K := hout (a + n) (by omega) (by omega)
    have hk2 : (leftAxisSite (a + n + 1) : Site 2) ∉ K := hout (a + n + 1) (by omega) (by omega)
    have hdiff : unitWt ((leftAxisSite (a + n) : Site 2) - leftAxisSite (a + n + 1)) = 1 := by
      unfold unitWt
      rw [Fin.sum_univ_two]
      have e0 : ((leftAxisSite (a + n) : Site 2) - leftAxisSite (a + n + 1)) 0 = 1 := by
        rw [leftAxisSite_succ_eq]
        simp [leftAxisSite, Pi.sub_apply]
      have e1 : ((leftAxisSite (a + n) : Site 2) - leftAxisSite (a + n + 1)) 1 = 0 := by
        rw [leftAxisSite_succ_eq]; simp [leftAxisSite, Pi.sub_apply]
      rw [e0, e1]; rfl
    have hstep := complReachable_of_unitDiff K hk1 hk2 hdiff
    have heq : (leftAxisSite (a + n + 1) : Site 2) = leftAxisSite (a + (n + 1)) := by
      have : a + n + 1 = a + (n + 1) := by omega
      rw [this]
    exact complReachable_congr (G := hypercubicLattice 2) (S := Kᶜ) rfl heq (h1.trans hstep)


theorem fdc_farLeftExitDart_head_reaches_axisFar (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ)
    (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
    ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).Reachable
      ⟨(fdc_farLeftExitDart (ω := ω) hfin R).head,
        (fdc_farLeftExitDart_isBoundaryDart (ω := ω) hfin R hR).2⟩
      ⟨leftAxisSite (R + 1), fdc_leftRun_not_mem (ω := ω) hfin R hR
        (Nat.succ_le_succ (fdc_leftExitIdx_le (ω := ω) hfin R)) (le_refl _)⟩ := by
  set n := fdc_leftExitIdx (ω := ω) hfin R with hn
  have hnR : n ≤ R := fdc_leftExitIdx_le (ω := ω) hfin R
  have hout : ∀ k, n + 1 ≤ k → k ≤ (n + 1) + (R - n) → (leftAxisSite k : Site 2)
      ∉ cluster 2 ω (origin 2) := by
    intro k hk1 hk2
    have hk2' : k ≤ R + 1 := by omega
    exact fdc_leftRun_not_mem (ω := ω) hfin R hR hk1 hk2'
  have hreach := fdc_leftAxis_reach (cluster 2 ω (origin 2)) (n + 1) (R - n) hout
  have heq : (leftAxisSite ((n + 1) + (R - n)) : Site 2) = leftAxisSite (R + 1) := by
    have : (n + 1) + (R - n) = R + 1 := by omega
    rw [this]
  exact complReachable_congr (G := hypercubicLattice 2) (S := (cluster 2 ω (origin 2))ᶜ)
    rfl heq hreach


theorem fdc_axisSite_eq_farRight (R : ℕ) : (axisSite (R + 1) : Site 2) = ![(R : ℤ) + 1, 0] := by
  funext i; fin_cases i <;> simp [axisSite]


theorem fdc_leftAxisSite_eq_farLeft (R : ℕ) :
    (leftAxisSite (R + 1) : Site 2) = ![-((R : ℤ) + 1), 0] := by
  rw [leftAxisSite_succ_eq]; funext i; fin_cases i <;> simp; ring


theorem fdc_farExitHeads_sameComponent (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ)
    (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
    ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).Reachable
      ⟨(fdc_farExitDart (ω := ω) hfin R).head,
        (fdc_farExitDart_isBoundaryDart (ω := ω) hfin R hR).2⟩
      ⟨(fdc_farLeftExitDart (ω := ω) hfin R).head,
        (fdc_farLeftExitDart_isBoundaryDart (ω := ω) hfin R hR).2⟩ := by
  
  have h1 := fdc_farExitDart_head_reaches_axisFar (ω := ω) hfin R hR
  
  have h2 := outC_axisFar_reachable (ω := ω) R hR
  
  have h3 := (fdc_farLeftExitDart_head_reaches_axisFar (ω := ω) hfin R hR).symm
  
  have h1' : ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).Reachable
      ⟨(fdc_farExitDart (ω := ω) hfin R).head,
        (fdc_farExitDart_isBoundaryDart (ω := ω) hfin R hR).2⟩
      ⟨(![(R : ℤ) + 1, 0] : Site 2), outC_axisFarRight_mem_compl (ω := ω) R hR⟩ :=
    complReachable_congr (G := hypercubicLattice 2) (S := (cluster 2 ω (origin 2))ᶜ)
      rfl (fdc_axisSite_eq_farRight R) h1
  have h3' : ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).Reachable
      ⟨(![-((R : ℤ) + 1), 0] : Site 2), outC_axisFarLeft_mem_compl (ω := ω) R hR⟩
      ⟨(fdc_farLeftExitDart (ω := ω) hfin R).head,
        (fdc_farLeftExitDart_isBoundaryDart (ω := ω) hfin R hR).2⟩ :=
    complReachable_congr (G := hypercubicLattice 2) (S := (cluster 2 ω (origin 2))ᶜ)
      (fdc_leftAxisSite_eq_farLeft R) rfl h3
  exact h1'.trans (h2.trans h3')


theorem fdc_farExitHeads_exterior (hfin : (cluster 2 ω (origin 2)).Finite) :
    outC_FarAxisHeadsFar ω hfin :=
  outC_farAxisHeadsFar_discharge (ω := ω) hfin


theorem fdc_farExitDartsSameOrbit (hfin : (cluster 2 ω (origin 2)).Finite)
    (hInt : InterfaceConnected (cluster 2 ω (origin 2)))
    (R : ℕ) (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
    ∃ n : ℕ, (dartNext (cluster 2 ω (origin 2)))^[n] (fdc_farExitDart (ω := ω) hfin R)
      = fdc_farLeftExitDart (ω := ω) hfin R :=
  hInt (fdc_farExitDart (ω := ω) hfin R) (fdc_farLeftExitDart (ω := ω) hfin R)
    (fdc_farExitDart_isBoundaryDart (ω := ω) hfin R hR)
    (fdc_farLeftExitDart_isBoundaryDart (ω := ω) hfin R hR)
    (fdc_farExitHeads_sameComponent (ω := ω) hfin R hR)


theorem fdc_sameOrbit_symm (K : Set (Site 2)) (hK : K.Finite) (e f : Dart)
    (he : IsBoundaryDart K e) {n : ℕ} (hn : (dartNext K)^[n] e = f) :
    ∃ m : ℕ, (dartNext K)^[m] f = e := by
  obtain ⟨p, hp, hper⟩ := dartNext_periodic K hK e he
  refine ⟨p * (n + 1) - n, ?_⟩
  rw [← hn, ← Function.iterate_add_apply]
  have hmn : p * (n + 1) - n + n = p * (n + 1) := by
    have : n ≤ p * (n + 1) := by nlinarith [hp]
    omega
  rw [hmn, Function.iterate_mul]
  have : (fun x => (dartNext K)^[p] x)^[n + 1] e = e := Function.iterate_fixed hper (n + 1)
  simpa using this


theorem fdc_sameOrbit_trans (K : Set (Site 2)) (e f g : Dart)
    {a b : ℕ} (ha : (dartNext K)^[a] e = f) (hb : (dartNext K)^[b] f = g) :
    ∃ c : ℕ, (dartNext K)^[c] e = g := by
  refine ⟨b + a, ?_⟩
  rw [Function.iterate_add_apply, ha, hb]


end Percolation
end StatMech
