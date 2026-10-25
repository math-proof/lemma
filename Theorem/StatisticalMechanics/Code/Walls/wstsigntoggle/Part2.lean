/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wstsigntoggle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.umffullrev.Part2
import Theorem.StatisticalMechanics.Code.Walls.wndwinding.Part3
import Theorem.StatisticalMechanics.Code.Walls.wnuupperhalf.Part5
import Theorem.StatisticalMechanics.Code.Walls.wnaalternate.Part3
import Def.StatisticalMechanics.Code.Walls.wstsigntoggle
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

theorem wst_columnAlternates_of_indicatorSteps (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (h : wst_IndicatorSteps z w) :
    wna_ColumnAlternates z w := by
  obtain ⟨M, ind, hperm, hpm, h0, hor, hL⟩ := h
  refine ⟨M, hperm, ?_⟩
  rcases hor with h01 | h0neg
  · exact wst_alt_of_indicatorSteps M ind hpm h01 h0 hL
  · exact wst_alt_of_indicatorSteps_neg M ind hpm h0neg h0 hL


theorem wst_signedCrossPMone_of_indicatorSteps (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (hstep : wst_IndicatorSteps z (olb_orbitLoop K hK a.1 a.2))
    (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2))) :
    wnd_SignedCrossPMone K hK a z :=
  wna_signedCrossPMone_of_columnAlternates K hK a z
    (wst_columnAlternates_of_indicatorSteps z (olb_orbitLoop K hK a.1 a.2) hstep) hodd


theorem wst_revCount_pm_one_of_indicatorSteps_bridge (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (hstep : wst_IndicatorSteps z (olb_orbitLoop K hK a.1 a.2))
    (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2)))
    (hbridge : wnd_SignedCrossEqRevCount K hK a z) :
    revCount K a = 1 ∨ revCount K a = -1 :=
  wna_revCount_pm_one_of_columnAlternates_bridge K hK a z
    (wst_columnAlternates_of_indicatorSteps z (olb_orbitLoop K hK a.1 a.2) hstep) hodd hbridge


theorem wst_eulerCharOne_of_indicatorSteps_bridge (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (hp : 3 ≤ dartOrbitPeriod K a)
    (hstep : wst_IndicatorSteps z (olb_orbitLoop K hK a.1 a.2))
    (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2)))
    (hbridge : wnd_SignedCrossEqRevCount K hK a z) :
    EulerCharOne K a :=
  wna_eulerCharOne_of_columnAlternates_bridge K hK a z hp
    (wst_columnAlternates_of_indicatorSteps z (olb_orbitLoop K hK a.1 a.2) hstep) hodd hbridge


theorem wst_unitSquare_indicatorSteps :
    wst_IndicatorSteps (![1, 1] : Site 2) wwit_unitSquareLoop := by
  refine ⟨[1], (fun n => if n = 0 then 0 else 1), ?_, ?_, ?_, ?_, ?_⟩
  · rw [wnu_unitSquare_signedList]
  · intro e he; simp at he; omega
  · simp
  · left; intro n; by_cases h : n = 0 <;> simp [h]
  · decide


theorem wst_Ltromino_indicatorSteps :
    wst_IndicatorSteps (![1, 1] : Site 2) wnu_LtrominoLoop := by
  refine ⟨[-1], (fun n => if n = 0 then 0 else -1), ?_, ?_, ?_, ?_, ?_⟩
  · rw [wnu_Ltromino_signedList]
  · intro e he; simp at he; omega
  · simp
  · right; intro n; by_cases h : n = 0 <;> simp [h]
  · decide


theorem wst_unitSquare_columnAlternates :
    wna_ColumnAlternates (![1, 1] : Site 2) wwit_unitSquareLoop :=
  wst_columnAlternates_of_indicatorSteps _ _ wst_unitSquare_indicatorSteps


theorem wst_Ltromino_columnAlternates :
    wna_ColumnAlternates (![1, 1] : Site 2) wnu_LtrominoLoop :=
  wst_columnAlternates_of_indicatorSteps _ _ wst_Ltromino_indicatorSteps


theorem wst_doubleSquare_not_indicatorSteps :
    ¬ wst_IndicatorSteps (![1, 1] : Site 2) wnu_doubleSquare := by
  rintro ⟨M, ind, hperm, hpm, h0, hor, hL⟩
  rw [wnu_doubleSquare_signedList] at hperm
  
  have hM : M = [1, 1] := by
    have hlen := hperm.length_eq
    have hmem : ∀ x ∈ M, x = 1 := by
      intro x hx
      have hx2 := hperm.mem_iff.mp hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx2
      rcases hx2 with h | h <;> exact h
    match M, hlen with
    | [a, b], _ =>
      have ha := hmem a (by simp); have hb := hmem b (by simp)
      rw [ha, hb]
  
  rw [hM] at hL
  simp only [List.length_cons, List.length_nil, List.range_succ, List.range_zero,
    List.map_append, List.map_cons, List.map_nil, List.nil_append] at hL
  
  have h1 : ind 1 - ind 0 = 1 := by
    have := congrArg (fun l => l[0]?) hL; simpa using this.symm
  have h2 : ind 2 - ind 1 = 1 := by
    have := congrArg (fun l => l[1]?) hL; simpa using this.symm
  have hind2 : ind 2 = 2 := by rw [h0] at h1; omega
  rcases hor with h | h <;> rcases h 2 with h' | h' <;> omega


theorem wst_doubleSquare_prefix_leaves_twoState :
    ∃ p ∈ wna_prefixSums [(1 : ℤ), 1], ¬ (p = 0 ∨ p = 1) ∧ ¬ (p = 0 ∨ p = -1) := by
  refine ⟨2, ?_, by omega, by omega⟩
  unfold wna_prefixSums; simp


end Lattice
end StatMech
