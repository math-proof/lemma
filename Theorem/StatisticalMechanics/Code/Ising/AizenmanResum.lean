/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanResum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Theorem.StatisticalMechanics.Code.Ising.AizenmanInclusionExclusion.Part3
import Theorem.StatisticalMechanics.Code.Ising.AizenmanHdom.Part2
import Notation.StatisticalMechanics.Code.Ising.AizenmanResum
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

open StatMech.Sharpness.RandomCurrent


local notation "srcK" => StatMech.Sharpness.RandomCurrent.sources

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


theorem ght_backbone_removed_subset (m P : Finset ι) (hP : P ⊆ m) : m ∆ P ⊆ m := by
  intro a ha
  rw [Finset.mem_symmDiff] at ha
  rcases ha with ⟨h, _⟩ | ⟨h, _⟩
  · exact h
  · exact hP h


theorem ght_backbone_removed_sources (ends : ι → Sym2 V) (m P : Finset ι) (A : Finset V)
    (hm : srcK ends m = A) {x y : V} (hPsrc : srcK ends P = {x, y}) :
    srcK ends (m ∆ P) = A ∆ {x, y} := by
  rw [sources_symmDiff, hm, hPsrc]


theorem ght_backbone_exists_xy (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hall : aie_allConn ends m o x y) (hxy : x ≠ y) :
    ∃ P ⊆ m, srcK ends P = {x, y} :=
  StatMech.Sharpness.RandomCurrent.exists_conn_set ends m hall.1 hxy


theorem ght_backbone_removed_nd (ends : ι → Sym2 V) (m P : Finset ι) (hP : P ⊆ m)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) :
    ∀ i ∈ m ∆ P, ¬ (ends i).IsDiag :=
  fun i hi => hnd i (ght_backbone_removed_subset m P hP hi)


theorem ght_backbone_per_switching (ends : ι → Sym2 V) (m P : Finset ι) (hP : P ⊆ m)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : srcK ends m = A)
    {x y : V} (hPsrc : srcK ends P = {x, y}) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K Q, Q ⊆ m ∆ P → K ⊆ m ∆ P → φ (K ∆ Q) = φ K) :
    aie_mass ends (m ∆ P) φ A
      = (if connK ends (m ∆ P) x y then 1 else 0) *
          aie_mass ends (m ∆ P) φ (A ∆ {x, y}) := by
  have hndP : ∀ i ∈ m ∆ P, ¬ (ends i).IsDiag :=
    ght_backbone_removed_nd ends m P hP hnd
  have hmP : srcK ends (m ∆ P) = A ∆ {x, y} :=
    ght_backbone_removed_sources ends m P A hm hPsrc
  have key := asd_switching_weighted_indicator ends (m ∆ P) hndP (A ∆ {x, y}) hmP hxy φ hφ
  have hAA : (A ∆ {x, y}) ∆ {x, y} = A := by
    rw [symmDiff_assoc, symmDiff_self, symmDiff_bot]
  rw [hAA] at key
  exact key


theorem ght_backbone_no_surplus_of_conn (ends : ι → Sym2 V) (m P : Finset ι) (hP : P ⊆ m)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : srcK ends m = A)
    {x y : V} (hPsrc : srcK ends P = {x, y}) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K Q, Q ⊆ m ∆ P → K ⊆ m ∆ P → φ (K ∆ Q) = φ K)
    (hconn : connK ends (m ∆ P) x y) :
    aie_mass ends (m ∆ P) φ (A ∆ {x, y}) = aie_mass ends (m ∆ P) φ A := by
  have key := ght_backbone_per_switching ends m P hP hnd A hm hPsrc hxy φ hφ
  rw [if_pos hconn, one_mul] at key
  exact key.symm


end Ising
end StatMech
