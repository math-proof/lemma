/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerClose2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer.Part3
import Def.StatisticalMechanics.Code.Inequalities.ReimerClose2.Part3
open MeasureTheory Finset
open scoped NNReal


namespace StatMech

open ConfigSpace

variable {E : Type*}


theorem reimerCore_succ_of_sliceStep (n : ℕ)
    (hcore : ∀ (φ : Fin n → Bool → ℝ), (∀ i b, 0 ≤ φ i b) → (∀ i, φ i false + φ i true = 1) →
      ∀ (A B : Set (ConfigSpace (Fin n))),
        wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B)
    (hstep : ReimerSliceStep n)
    (φ : Fin (n + 1) → Bool → ℝ) (hφ0 : ∀ i b, 0 ≤ φ i b) (hφ1 : ∀ i, φ i false + φ i true = 1)
    (A B : Set (ConfigSpace (Fin (n + 1)))) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
  set ψ : Fin n → Bool → ℝ := fun j => φ j.succ with hψ
  have hψ0 : ∀ i b, 0 ≤ ψ i b := fun i b => hφ0 i.succ b
  have hψ1 : ∀ i, ψ i false + ψ i true = 1 := fun i => hφ1 i.succ
  set q := φ 0 false with hqdef
  set p := φ 0 true with hpdef
  have hq0 : 0 ≤ q := hφ0 0 false
  have hp0 : 0 ≤ p := hφ0 0 true
  have hqp : q + p = 1 := hφ1 0
  have hqeq : q = 1 - p := by linarith
  set A0 := slice A false
  set A1 := slice A true
  set B0 := slice B false
  set B1 := slice B true
  set a0 := wprob ψ A0
  set a1 := wprob ψ A1
  set b0 := wprob ψ B0
  set b1 := wprob ψ B1
  have indA0B0 : wprob ψ (disjointOccurrence A0 B0) ≤ a0 * b0 := hcore ψ hψ0 hψ1 A0 B0
  have indU : wprob ψ (disjointOccurrence A0 B1) ≤ a0 * b1 := hcore ψ hψ0 hψ1 A0 B1
  have indV : wprob ψ (disjointOccurrence A1 B0) ≤ a1 * b0 := hcore ψ hψ0 hψ1 A1 B0
  set U := disjointOccurrence A0 B1 with hU
  set V := disjointOccurrence A1 B0 with hV
  set m := wprob ψ (disjointOccurrence A0 B0) with hm
  set c0 := wprob ψ (slice (disjointOccurrence A B) false) with hc0
  set c1 := wprob ψ (slice (disjointOccurrence A B) true) with hc1
  have hc0m : c0 ≤ m := wprob_mono hψ0 slice_disjointOccurrence_false
  have hc1UV : c1 ≤ wprob ψ (U ∪ V) := wprob_mono hψ0 slice_disjointOccurrence_true
  have hincl : wprob ψ (U ∪ V) = wprob ψ U + wprob ψ V - wprob ψ (U ∩ V) := by
    have := wprob_union_inter ψ U V; linarith
  obtain ⟨hmUV, hc1top⟩ := hstep ψ hψ0 hψ1 A B
  have hc1v : c1 ≤ a1 * b1 := le_trans hc1UV hc1top
  have hc1u : c1 ≤ a0 * b1 + a1 * b0 - m := by
    calc c1 ≤ wprob ψ (U ∪ V) := hc1UV
      _ = wprob ψ U + wprob ψ V - wprob ψ (U ∩ V) := hincl
      _ ≤ a0 * b1 + a1 * b0 - m := by linarith [indU, indV, hmUV]
  have hmab : m ≤ a0 * b0 := indA0B0
  have hdec : wprob φ (disjointOccurrence A B) = q * c0 + p * c1 := by rw [wprob_slice]
  have hAdec : wprob φ A = q * a0 + p * a1 := by rw [wprob_slice]
  have hBdec : wprob φ B = q * b0 + p * b1 := by rw [wprob_slice]
  rw [hdec, hAdec, hBdec]
  exact bk_algebra a0 a1 b0 b1 p q c0 c1 m hqeq hp0 hq0 hmab hc0m hc1u hc1v


theorem reimer_wprobCore_of_sliceStep (hstep : ∀ n, ReimerSliceStep n) : ReimerWprobCore := by
  intro n
  induction n with
  | zero => intro φ _ _ A B; exact reimer_wprob_zero φ A B
  | succ n ih =>
      intro φ hφ0 hφ1 A B
      exact reimerCore_succ_of_sliceStep n
        (fun ψ hψ0 hψ1 C D => ih ψ hψ0 hψ1 C D) (hstep n) φ hφ0 hφ1 A B


theorem reimerSliceStep_holds_on_increasing (n : ℕ) (ψ : Fin n → Bool → ℝ)
    (hψ0 : ∀ i b, 0 ≤ ψ i b) (hψ1 : ∀ i, ψ i false + ψ i true = 1)
    (A B : Set (ConfigSpace (Fin (n + 1)))) (hA : IsIncreasing A) (hB : IsIncreasing B) :
    wprob ψ (disjointOccurrence (slice A false) (slice B false))
        ≤ wprob ψ (disjointOccurrence (slice A false) (slice B true)
                    ∩ disjointOccurrence (slice A true) (slice B false))
    ∧ wprob ψ (disjointOccurrence (slice A false) (slice B true)
                ∪ disjointOccurrence (slice A true) (slice B false))
        ≤ wprob ψ (slice A true) * wprob ψ (slice B true) := by
  have hA1 : IsIncreasing (slice A true) := slice_isIncreasing hA true
  have hB1 : IsIncreasing (slice B true) := slice_isIncreasing hB true
  have hA01 : slice A false ⊆ slice A true := slice_false_subset_true hA
  have hB01 : slice B false ⊆ slice B true := slice_false_subset_true hB
  refine ⟨?_, ?_⟩
  · refine wprob_mono hψ0 ?_
    exact Set.subset_inter (disjointOccurrence_mono (le_refl _) hB01)
      (disjointOccurrence_mono hA01 (le_refl _))
  · calc wprob ψ (disjointOccurrence (slice A false) (slice B true)
                  ∪ disjointOccurrence (slice A true) (slice B false))
        ≤ wprob ψ (disjointOccurrence (slice A true) (slice B true)) := by
          refine wprob_mono hψ0 ?_
          exact Set.union_subset (disjointOccurrence_mono hA01 (le_refl _))
            (disjointOccurrence_mono (le_refl _) hB01)
      _ ≤ wprob ψ (slice A true) * wprob ψ (slice B true) := bk_wprob n ψ hψ0 hψ1 _ _ hA1 hB1


theorem reimerSliceStep_satisfiable (n : ℕ) (ψ : Fin n → Bool → ℝ)
    (hψ0 : ∀ i b, 0 ≤ ψ i b) (hψ1 : ∀ i, ψ i false + ψ i true = 1) :
    wprob ψ (disjointOccurrence (slice (Set.univ : Set (ConfigSpace (Fin (n + 1)))) false)
              (slice (Set.univ : Set (ConfigSpace (Fin (n + 1)))) false))
        ≤ wprob ψ (disjointOccurrence (slice (Set.univ : Set (ConfigSpace (Fin (n + 1)))) false)
                    (slice Set.univ true)
                    ∩ disjointOccurrence (slice Set.univ true) (slice Set.univ false))
    ∧ wprob ψ (disjointOccurrence (slice (Set.univ : Set (ConfigSpace (Fin (n + 1)))) false)
                (slice Set.univ true)
                ∪ disjointOccurrence (slice Set.univ true) (slice Set.univ false))
        ≤ wprob ψ (slice (Set.univ : Set (ConfigSpace (Fin (n + 1)))) true)
            * wprob ψ (slice Set.univ true) :=
  reimerSliceStep_holds_on_increasing n ψ hψ0 hψ1 Set.univ Set.univ
    (isUpperSet_univ) (isUpperSet_univ)


end StatMech
