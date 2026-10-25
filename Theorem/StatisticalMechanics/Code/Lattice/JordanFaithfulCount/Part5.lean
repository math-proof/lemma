/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanOuterFaceUnique.Part3
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleRank.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationFinish.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
import Def.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part4
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jfc_faithfulCountResidue_of_threading (hthr : jfc_EvenDegreeThreading) :
    jeb_FaithfulCountResidue :=
  fun P hP => jfc_faithfulDiscreteJordan_of_sync P (hthr P hP)


theorem jfc_evenDegreeThreading_of_bot {P : PlanarZ2Subgraph} (hG : P.G = ⊥) :
    jfc_WhbSync P := by
  intro K _ x y hadjG _ _ _ _ _
  rw [hG] at hadjG
  exact absurd hadjG (by simp)


theorem jfc_latadj_E (a b : ℤ) : (hypercubicLattice 2).Adj ![a, b] ![a + 1, b] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp

theorem jfc_latadj_N (a b : ℤ) : (hypercubicLattice 2).Adj ![a, b] ![a, b + 1] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp


theorem jfc_sq_adj_of_ne_origin {f g : Site 2} (hadj : (hypercubicLattice 2).Adj f g)
    (hf : f ≠ ![0, 0]) (hg : g ≠ ![0, 0]) :
    (whb_faceRegion (imageGraph jbc_Pce)).Adj f g := by
  refine ⟨hadj, ?_⟩
  intro hmem
  rw [whc_shared_mem_square_iff f g hadj] at hmem
  rcases hmem with h | h | h | h <;>
    (rw [Sym2.eq_iff] at h;
     rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> first | exact hf rfl | exact hg rfl)


theorem jfc_sq_row_east (b : ℤ) (hb : b ≠ 0) (a : ℤ) (n : ℕ) :
    (whb_faceRegion (imageGraph jbc_Pce)).Reachable ![a, b] ![a + n, b] := by
  induction n with
  | zero => simp
  | succ k ih =>
    refine ih.trans ?_
    have e : (![a + (↑(k + 1) : ℤ), b] : Site 2) = ![(a + (k : ℤ)) + 1, b] := by
      push_cast; funext i; fin_cases i <;> simp <;> ring
    rw [e]
    apply (jfc_sq_adj_of_ne_origin (jfc_latadj_E _ _) ?_ ?_).reachable
    · intro h; have := congrFun h 1; simp at this; omega
    · intro h; have := congrFun h 1; simp at this; omega


theorem jfc_sq_col_north (a : ℤ) (ha : a ≠ 0) (b : ℤ) (n : ℕ) :
    (whb_faceRegion (imageGraph jbc_Pce)).Reachable ![a, b] ![a, b + n] := by
  induction n with
  | zero => simp
  | succ k ih =>
    refine ih.trans ?_
    have e : (![a, b + (↑(k + 1) : ℤ)] : Site 2) = ![a, (b + (k : ℤ)) + 1] := by
      push_cast; funext i; fin_cases i <;> simp <;> ring
    rw [e]
    apply (jfc_sq_adj_of_ne_origin (jfc_latadj_N _ _) ?_ ?_).reachable
    · intro h; have := congrFun h 0; simp at this; omega
    · intro h; have := congrFun h 0; simp at this; omega


theorem jfc_sq_farEast_exterior (M : ℕ) (a b : ℤ) :
    (![a + ((M + 1 + a.natAbs : ℕ) : ℤ), b] : Site 2) ∈ exterior 2 M := by
  rw [mem_exterior]
  refine ⟨0, ?_⟩
  have h : ((M + 1 + a.natAbs : ℕ) : ℤ) = (M : ℤ) + 1 + (a.natAbs : ℤ) := by push_cast; ring
  simp only [Matrix.cons_val_zero, h]
  omega


theorem jfc_sq_reach_outerRegion {v : Site 2} (hv : v ≠ ![0, 0]) :
    (whb_faceRegion (imageGraph jbc_Pce)).connectedComponentMk v = jfc_whb_outerRegion jbc_Pce := by
  set R := outerBoxRadius jbc_Pce with hR
  
  have hvform : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  
  by_cases hv1 : v 1 = 0
  · 
    have hv0 : v 0 ≠ 0 := by
      intro h; exact hv (by rw [hvform, h, hv1])
    have hnorth : (whb_faceRegion (imageGraph jbc_Pce)).Reachable ![v 0, v 1] ![v 0, v 1 + 1] := by
      have h := jfc_sq_col_north (v 0) hv0 (v 1) 1
      simpa using h
    have heast := jfc_sq_row_east (v 1 + 1) (by omega) (v 0)
        (R + 1 + 1 + (v 0).natAbs)
    have hext : (![v 0 + ((R + 1 + 1 + (v 0).natAbs : ℕ) : ℤ), v 1 + 1] : Site 2)
        ∈ exterior 2 (R + 1) := jfc_sq_farEast_exterior (R + 1) (v 0) (v 1 + 1)
    have hmk := jfc_whb_exterior_in_outerRegion jbc_Pce hext
    rw [hvform]
    calc (whb_faceRegion (imageGraph jbc_Pce)).connectedComponentMk ![v 0, v 1]
        = (whb_faceRegion (imageGraph jbc_Pce)).connectedComponentMk
            ![v 0 + ((R + 1 + 1 + (v 0).natAbs : ℕ) : ℤ), v 1 + 1] :=
          ConnectedComponent.sound (hnorth.trans heast)
      _ = jfc_whb_outerRegion jbc_Pce := hmk
  · 
    have heast := jfc_sq_row_east (v 1) hv1 (v 0) (R + 1 + 1 + (v 0).natAbs)
    have hext : (![v 0 + ((R + 1 + 1 + (v 0).natAbs : ℕ) : ℤ), v 1] : Site 2)
        ∈ exterior 2 (R + 1) := jfc_sq_farEast_exterior (R + 1) (v 0) (v 1)
    have hmk := jfc_whb_exterior_in_outerRegion jbc_Pce hext
    rw [hvform]
    calc (whb_faceRegion (imageGraph jbc_Pce)).connectedComponentMk ![v 0, v 1]
        = (whb_faceRegion (imageGraph jbc_Pce)).connectedComponentMk
            ![v 0 + ((R + 1 + 1 + (v 0).natAbs : ℕ) : ℤ), v 1] :=
          ConnectedComponent.sound heast
      _ = jfc_whb_outerRegion jbc_Pce := hmk


end Lattice
end StatMech
