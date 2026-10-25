/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanSignDominance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Ising.TwoReplica.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Ising.TwoReplicaWeighted.Part2
import Def.StatisticalMechanics.Code.Ising.AizenmanSignDominance
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

namespace RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


theorem asd_ghsBackboneFactor_allConn (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hxy : connK ends m x y) (hoy : connK ends m o y) (hox : connK ends m o x) :
    asd_ghsBackboneFactor ends m o x y = -2 := by
  unfold asd_ghsBackboneFactor
  rw [if_pos hxy, if_pos hoy, if_pos hox]; norm_num


theorem asd_ghsBackboneFactor_noConn (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hxy : ¬ connK ends m x y) (hoy : ¬ connK ends m o y) (hox : ¬ connK ends m o x) :
    asd_ghsBackboneFactor ends m o x y = 1 := by
  unfold asd_ghsBackboneFactor
  rw [if_neg hxy, if_neg hoy, if_neg hox]; norm_num


theorem asd_ghsBackboneFactor_not_signDefinite (ends : ι → Sym2 V) (m₁ m₂ : Finset ι)
    {o x y : V}
    (h₁ : connK ends m₁ x y ∧ connK ends m₁ o y ∧ connK ends m₁ o x)
    (h₂ : ¬ connK ends m₂ x y ∧ ¬ connK ends m₂ o y ∧ ¬ connK ends m₂ o x) :
    asd_ghsBackboneFactor ends m₁ o x y < 0
      ∧ 0 < asd_ghsBackboneFactor ends m₂ o x y := by
  obtain ⟨hxy₁, hoy₁, hox₁⟩ := h₁
  obtain ⟨hxy₂, hoy₂, hox₂⟩ := h₂
  refine ⟨?_, ?_⟩
  · rw [asd_ghsBackboneFactor_allConn ends m₁ hxy₁ hoy₁ hox₁]; norm_num
  · rw [asd_ghsBackboneFactor_noConn ends m₂ hxy₂ hoy₂ hox₂]; norm_num


theorem asd_ghsBackboneFactor_nonneg_singleBackbone (ends : ι → Sym2 V) (m : Finset ι)
    {o x y : V}
    (h : ¬ (connK ends m x y ∧ connK ends m o y) ∧ ¬ (connK ends m x y ∧ connK ends m o x)
        ∧ ¬ (connK ends m o y ∧ connK ends m o x)) :
    0 ≤ asd_ghsBackboneFactor ends m o x y := by
  obtain ⟨h12, h13, h23⟩ := h
  unfold asd_ghsBackboneFactor
  by_cases hxy : connK ends m x y <;> by_cases hoy : connK ends m o y <;>
    by_cases hox : connK ends m o x <;> simp_all


theorem asd_ghsSigned_nonneg_singleBackbone (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφnn : ∀ K, 0 ≤ φ K) (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hsingle : ¬ (connK ends m x y ∧ connK ends m o y)
        ∧ ¬ (connK ends m x y ∧ connK ends m o x)
        ∧ ¬ (connK ends m o y ∧ connK ends m o x)) :
    0 ≤ (∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K)
          - (∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {x, y}), φ K)
          - (∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {o, y}), φ K)
          - (∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {o, x}), φ K) := by
  rw [asd_ghsSigned_eq ends m hnd A hm hox hoy hxy φ hφ]
  apply mul_nonneg (Finset.sum_nonneg (fun K _ => hφnn K))
  exact asd_ghsBackboneFactor_nonneg_singleBackbone ends m hsingle


theorem asd_switching_weighted₂_edgecopy (ends : ι → Sym2 V) (m P Q : Finset ι)
    (hP : P ⊆ m) (hQ : Q ⊆ m) (A : Finset V) (φ : Finset ι → ℝ)
    (hφ : ∀ K, K ⊆ m → φ ((K ∆ P) ∆ Q) = φ K) :
    ∑ K ∈ m.powerset.filter
        (fun K => sources ends K = A ∆ sources ends P ∆ sources ends Q), φ K
      = ∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K := by
  have hbij := sources_shift₂_bijOn ends m P Q hP hQ A
  have himg : (m.powerset.filter
        (fun K => sources ends K = A ∆ sources ends P ∆ sources ends Q))
      = (m.powerset.filter (fun K => sources ends K = A)).image (fun K => (K ∆ P) ∆ Q) := by
    ext K
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · intro ⟨hKm, hKsrc⟩
      obtain ⟨L, hL, hLK⟩ := hbij.2.2 ⟨hKm, hKsrc⟩
      exact ⟨L, ⟨hL.1, hL.2⟩, hLK⟩
    · rintro ⟨L, ⟨hLm, hLsrc⟩, rfl⟩
      have := hbij.1 ⟨hLm, hLsrc⟩
      exact ⟨this.1, this.2⟩
  rw [himg, Finset.sum_image]
  · exact Finset.sum_congr rfl (fun K hK => by
      simp only [Finset.mem_filter, Finset.mem_powerset] at hK; exact hφ K hK.1)
  · intro K₁ hK₁ K₂ hK₂ h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hK₁ hK₂
    exact hbij.2.1 ⟨hK₁.1, hK₁.2⟩ ⟨hK₂.1, hK₂.2⟩ h


theorem asd_signDominance₂_edgecopy (ends : ι → Sym2 V) (m : Finset ι)
    (A : Finset V) {u v s t : V} (huv : u ≠ v) (hst : s ≠ t)
    (hconnuv : connK ends m u v) (hconnst : connK ends m s t) (φ : Finset ι → ℝ)
    (hφ : ∀ K P Q, P ⊆ m → Q ⊆ m → K ⊆ m → φ ((K ∆ P) ∆ Q) = φ K) :
    ∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {u, v} ∆ {s, t}), φ K
      = ∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K := by
  obtain ⟨P, hPm, hPsrc⟩ := exists_conn_set ends m hconnuv huv
  obtain ⟨Q, hQm, hQsrc⟩ := exists_conn_set ends m hconnst hst
  have := asd_switching_weighted₂_edgecopy ends m P Q hPm hQm A φ
    (fun K hK => hφ K P Q hPm hQm hK)
  rwa [hPsrc, hQsrc] at this

end RandomCurrent

end Sharpness


namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem asd_signCancel_native (β : ℝ) (J : Sym2 V → ℝ) (m : Current V)
    {u v : V} (huv : u ≠ v) (hconn : connP (oddEdges G.edgeFinset m) u v)
    (F : ℝ) (A : Finset V) :
    splitWeightedSum G β J m F (A ∆ {u, v}) = splitWeightedSum G β J m F A :=
  ising_switching_weighted G β J m huv hconn F A


theorem asd_signDominance_native (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (m : Current V) (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (F : ℝ) (hF : 0 ≤ F)
    (A : Finset V) (hm : Sharpness.sources G m = A) {u v : V} (huv : u ≠ v)
    (hconn_odd_or_disc :
      connP (oddEdges G.edgeFinset m) u v ∨ ¬ connP (posEdges G.edgeFinset m) u v) :
    splitWeightedSum G β J m F (A ∆ {u, v}) ≤ splitWeightedSum G β J m F A := by
  rcases hconn_odd_or_disc with hconn | hdisc
  · rw [asd_signCancel_native G β J m huv hconn F A]
  · rw [ising_switching_weighted_vanishing G β J m hnd A hm huv hdisc F]
    exact asd_splitWeightedSum_nonneg G β J hβ hJ m F hF A


theorem asd_signDominance_derived (β : ℝ) (J : Sym2 V → ℝ) (m : Current V)
    (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (F : ℝ) {u v : V} (huv : u ≠ v)
    (hsrc : Sharpness.sources G m = {u, v}) :
    splitWeightedSum G β J m F {u, v} = splitWeightedSum G β J m F ∅ :=
  ising_switching_weighted_sourceless G β J m hnd huv hsrc F

end Ising
end StatMech
