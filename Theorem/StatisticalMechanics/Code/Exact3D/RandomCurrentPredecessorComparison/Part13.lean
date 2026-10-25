/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part12
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem edgeCopySourcePairDataWitnessAt_mem_witnesses
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (m : ↥G.edgeFinset → ℕ)
    (d : edgeCopySourcePairData G A B)
    (hdm : d.1 = m) :
    edgeCopySourcePairDataWitnessAt G m d ∈
      edgeCopySourcePairWitnesses G A B m := by
  subst m
  simpa [edgeCopySourcePairDataWitnessAt] using
    edgeCopySourcePairData_mem_witnesses G d

set_option linter.style.longLine false in


theorem edgeCopySourcePairData_eq_of_profile_eq_of_witnessAt_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (m : ↥G.edgeFinset → ℕ)
    {d e : edgeCopySourcePairData G A B}
    (hdm : d.1 = m) (hem : e.1 = m)
    (hW :
      edgeCopySourcePairDataWitnessAt G m d =
        edgeCopySourcePairDataWitnessAt G m e) :
    d = e := by
  classical
  rcases d with ⟨md, Kd, hKd⟩
  rcases e with ⟨me, Ke, hKe⟩
  dsimp at hdm hem hW ⊢
  subst md
  subst me
  have hK : Kd = Ke := by
    simpa [edgeCopySourcePairDataWitnessAt] using hW
  subst Ke
  simp

set_option linter.style.longLine false in


theorem edgeCopySourcePairData_profileFiber_card_le_witnesses
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V)
    (t : Finset (edgeCopySourcePairData G A B))
    (m : ↥G.edgeFinset → ℕ) :
    (((t.filter fun d => d.1 = m).card : ℕ) : ℝ) ≤
      ((edgeCopySourcePairWitnesses G A B m).card : ℝ) := by
  classical
  have hcard_nat :
      (t.filter fun d => d.1 = m).card ≤
        (edgeCopySourcePairWitnesses G A B m).card := by
    refine
      Finset.card_le_card_of_injOn
        (edgeCopySourcePairDataWitnessAt G (A := A) (B := B) m) ?_ ?_
    · intro d hd
      exact
        edgeCopySourcePairDataWitnessAt_mem_witnesses G m d
          (Finset.mem_filter.mp hd).2
    · intro d hd e he hW
      exact
        edgeCopySourcePairData_eq_of_profile_eq_of_witnessAt_eq G m
          (Finset.mem_filter.mp hd).2 (Finset.mem_filter.mp he).2 hW
  exact_mod_cast hcard_nat

set_option linter.style.longLine false in


theorem copyDeletePreimageDecrementEraseFinset_injective_of_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ)
    (i : Sharpness.FluxEdgeCopy.Copy G m)
    {K L : Finset (Sharpness.FluxEdgeCopy.Copy G m)}
    (hiK : i ∈ K) (hiL : i ∈ L)
    (hmap :
      copyDeletePreimageDecrementEraseFinset G m i K =
        copyDeletePreimageDecrementEraseFinset G m i L) :
    K = L := by
  classical
  have hback := congrArg (copyDeleteEmbeddingDecrementFinset G m i) hmap
  rw [copyDeleteEmbeddingDecrementFinset_preimageErase,
    copyDeleteEmbeddingDecrementFinset_preimageErase] at hback
  rw [← Finset.insert_erase hiK, hback, Finset.insert_erase hiL]

set_option linter.style.longLine false in


theorem copyDeletePreimageDecrementEraseFinset_injective_of_not_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ)
    (i : Sharpness.FluxEdgeCopy.Copy G m)
    {K L : Finset (Sharpness.FluxEdgeCopy.Copy G m)}
    (hiK : i ∉ K) (hiL : i ∉ L)
    (hmap :
      copyDeletePreimageDecrementEraseFinset G m i K =
        copyDeletePreimageDecrementEraseFinset G m i L) :
    K = L := by
  classical
  have hback := congrArg (copyDeleteEmbeddingDecrementFinset G m i) hmap
  rw [copyDeleteEmbeddingDecrementFinset_preimageErase,
    copyDeleteEmbeddingDecrementFinset_preimageErase] at hback
  rwa [Finset.erase_eq_of_notMem hiK, Finset.erase_eq_of_notMem hiL] at hback

set_option linter.style.longLine false in


theorem edgeCopySourcePairSummand_eq_witness_card_mul_weight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (m : ↥G.edgeFinset → ℕ) :
    edgeCopySourcePairSummand G β J A B m =
      ((edgeCopySourcePairWitnesses G A B m).card : ℝ) *
        Sharpness.weight G β J (Sharpness.ofEdgeFun G m) := by
  classical
  let C := Sharpness.FluxEdgeCopy.Copy G m
  let ends := Sharpness.FluxEdgeCopy.endsM G m
  let wt := Sharpness.weight G β J (Sharpness.ofEdgeFun G m)
  have hind :
      (∑ S : Finset C,
        (if Sharpness.RandomCurrent.sources ends S = A then (1 : ℝ) else 0) *
          (if Sharpness.RandomCurrent.sources ends
              ((Finset.univ : Finset C) \ S) = B then (1 : ℝ) else 0)) =
        ((edgeCopySourcePairWitnesses G A B m).card : ℝ) := by
    have hfilter :
        (∑ S ∈ edgeCopySourcePairWitnesses G A B m, (1 : ℝ)) =
          ((edgeCopySourcePairWitnesses G A B m).card : ℝ) := by
      simp
    rw [← hfilter]
    rw [edgeCopySourcePairWitnesses]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro S _hS
    by_cases hA : Sharpness.RandomCurrent.sources ends S = A
    · rw [if_pos hA]
      by_cases hB :
          Sharpness.RandomCurrent.sources ends
            ((Finset.univ : Finset C) \ S) = B
      · rw [if_pos hB]
        have hP :
            Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM G m) S = A ∧
              Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM G m)
                ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) \ S) = B := by
          exact ⟨by simpa [ends] using hA, by simpa [ends, C] using hB⟩
        rw [if_pos hP]
        norm_num
      · rw [if_neg hB]
        have hP :
            ¬(Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM G m) S = A ∧
              Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM G m)
                ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) \ S) = B) := by
          intro h
          exact hB (by simpa [ends, C] using h.2)
        rw [if_neg hP]
        norm_num
    · rw [if_neg hA]
      have hP :
          ¬(Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM G m) S = A ∧
            Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM G m)
              ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) \ S) = B) := by
        intro h
        exact hA (by simpa [ends] using h.1)
      rw [if_neg hP]
      norm_num
  unfold edgeCopySourcePairSummand
  change
    (∑ S : Finset C,
      (if Sharpness.RandomCurrent.sources ends S = A then (1 : ℝ) else 0) *
        (if Sharpness.RandomCurrent.sources ends
            ((Finset.univ : Finset C) \ S) = B then (1 : ℝ) else 0)) * wt =
      ((edgeCopySourcePairWitnesses G A B m).card : ℝ) * wt
  rw [hind]

set_option linter.style.longLine false in


theorem
    edgeCopySourcePairDataWeight_finset_sum_le_sourcePairSum_of_profileFiber_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V)
    (t : Finset (edgeCopySourcePairData G A B))
    (hfiber :
      ∀ m ∈ t.image (fun d => d.1),
        ((t.filter fun d => d.1 = m).card : ℝ) ≤
          ((edgeCopySourcePairWitnesses G A B m).card : ℝ)) :
    (∑ d ∈ t, edgeCopySourcePairDataWeight G β J d) ≤
      Sharpness.sourcePairSum G β J A B := by
  classical
  let I : FinsetFiberIndex (↥G.edgeFinset → ℕ) := {
    α := edgeCopySourcePairData G A B
    domain := t
    map := fun d => d.1 }
  let W : (↥G.edgeFinset → ℕ) → ℝ :=
    fun m => Sharpness.weight G β J (Sharpness.ofEdgeFun G m)
  have hregroup :
      (∑ d ∈ t, edgeCopySourcePairDataWeight G β J d) =
        ∑ m ∈ I.image, (((I.fiber m).card : ℝ) * W m) := by
    change Finset.sum I.domain (fun d => W (I.map d)) =
      ∑ m ∈ I.image, (((I.fiber m).card : ℝ) * W m)
    exact FinsetFiberIndex.sum_fiber_weight I W
  calc
    (∑ d ∈ t, edgeCopySourcePairDataWeight G β J d) =
        ∑ m ∈ I.image, (((I.fiber m).card : ℝ) * W m) :=
      hregroup
    _ ≤ ∑ m ∈ I.image, edgeCopySourcePairSummand G β J A B m := by
      refine Finset.sum_le_sum ?_
      intro m hm
      have hcard :
          (((I.fiber m).card : ℕ) : ℝ) ≤
            ((edgeCopySourcePairWitnesses G A B m).card : ℝ) := by
        simpa [I, FinsetFiberIndex.fiber, FinsetFiberIndex.image] using
          hfiber m (by simpa [I, FinsetFiberIndex.image] using hm)
      have hW_nonneg : 0 ≤ W m := by
        dsimp [W]
        exact weight_ofEdgeFun_nonneg_of_nonneg G β J hβ hJ m
      calc
        (((I.fiber m).card : ℝ) * W m) ≤
            ((edgeCopySourcePairWitnesses G A B m).card : ℝ) * W m :=
          mul_le_mul_of_nonneg_right hcard hW_nonneg
        _ = edgeCopySourcePairSummand G β J A B m := by
          exact (edgeCopySourcePairSummand_eq_witness_card_mul_weight
            G β J A B m).symm
    _ ≤ ∑' m : ↥G.edgeFinset → ℕ, edgeCopySourcePairSummand G β J A B m :=
      (edgeCopySourcePairSummand_summable G β J A B).sum_le_tsum
        I.image
        (fun m _hm => edgeCopySourcePairSummand_nonneg G β J A B m hβ hJ)
    _ = Sharpness.sourcePairSum G β J A B := by
      rw [sourcePairSum_eq_edgeCopySourcePairSum]
      rfl

set_option linter.style.longLine false in


theorem edgeCopySourcePairDataWeight_finset_sum_le_sourcePairSum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V)
    (t : Finset (edgeCopySourcePairData G A B)) :
    (∑ d ∈ t, edgeCopySourcePairDataWeight G β J d) ≤
      Sharpness.sourcePairSum G β J A B :=
  edgeCopySourcePairDataWeight_finset_sum_le_sourcePairSum_of_profileFiber_card_le
    G hβ J hJ A B t
    (fun m _hm =>
      edgeCopySourcePairData_profileFiber_card_le_witnesses G A B t m)

set_option linter.style.longLine false in


theorem
    edgeCopySourcePairDataWeight_finset_sum_route_le_sourcePairSum_of_injOn_profileFiber_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V)
    {α : Type*} (s : Finset α)
    (route : α → edgeCopySourcePairData G A B)
    (hinj : Set.InjOn route s)
    (hfiber :
      ∀ m ∈ (s.image route).image (fun d => d.1),
        (((s.image route).filter fun d => d.1 = m).card : ℝ) ≤
          ((edgeCopySourcePairWitnesses G A B m).card : ℝ)) :
    (∑ a ∈ s, edgeCopySourcePairDataWeight G β J (route a)) ≤
      Sharpness.sourcePairSum G β J A B := by
  classical
  calc
    (∑ a ∈ s, edgeCopySourcePairDataWeight G β J (route a)) =
        ∑ d ∈ s.image route, edgeCopySourcePairDataWeight G β J d := by
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact hinj ha hb hab
    _ ≤ Sharpness.sourcePairSum G β J A B :=
      edgeCopySourcePairDataWeight_finset_sum_le_sourcePairSum_of_profileFiber_card_le
        G hβ J hJ A B (s.image route) hfiber

set_option linter.style.longLine false in


theorem
    edgeCopySourcePairDataWeight_finset_sum_route_le_sourcePairSum_of_injOn
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V)
    {α : Type*} (s : Finset α)
    (route : α → edgeCopySourcePairData G A B)
    (hinj : Set.InjOn route s) :
    (∑ a ∈ s, edgeCopySourcePairDataWeight G β J (route a)) ≤
      Sharpness.sourcePairSum G β J A B := by
  classical
  calc
    (∑ a ∈ s, edgeCopySourcePairDataWeight G β J (route a)) =
        ∑ d ∈ s.image route, edgeCopySourcePairDataWeight G β J d := by
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact hinj ha hb hab
    _ ≤ Sharpness.sourcePairSum G β J A B :=
      edgeCopySourcePairDataWeight_finset_sum_le_sourcePairSum
        G hβ J hJ A B (s.image route)

set_option linter.style.longLine false in


theorem
    edgeCopySourcePairDataWeight_finset_sum_route_beta_div_six_le_sourcePairSum_of_injOn
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V)
    {α : Type*} (s : Finset α)
    (route : α → edgeCopySourcePairData G A B)
    (hinj : Set.InjOn route s) :
    (∑ a ∈ s, (β / 6) * edgeCopySourcePairDataWeight G β J (route a)) ≤
      (β / 6) * Sharpness.sourcePairSum G β J A B := by
  have hcoef : 0 ≤ β / 6 := by positivity
  rw [← Finset.mul_sum]
  exact
    mul_le_mul_of_nonneg_left
      (edgeCopySourcePairDataWeight_finset_sum_route_le_sourcePairSum_of_injOn
        G hβ J hJ A B s route hinj)
      hcoef

set_option linter.style.longLine false in


theorem
    edgeCopySourcePairDataWeight_finset_attach_sum_route_beta_div_six_le_sourcePairSum_of_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V)
    {α : Type*} (s : Finset α)
    (route : {a : α // a ∈ s} → edgeCopySourcePairData G A B)
    (hinj : Function.Injective route) :
    (∑ a ∈ s.attach,
        (β / 6) * edgeCopySourcePairDataWeight G β J (route a)) ≤
      (β / 6) * Sharpness.sourcePairSum G β J A B := by
  exact
    edgeCopySourcePairDataWeight_finset_sum_route_beta_div_six_le_sourcePairSum_of_injOn
      G hβ J hJ A B s.attach route
      (by
        intro a _ha b _hb hab
        exact hinj hab)

set_option linter.style.longLine false in


theorem
    edgeCopySourcePairDataWeight_finset_sum_route_beta_div_six_div_384_le_sourcePairShare_of_injOn
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V)
    {α : Type*} (s : Finset α)
    (route : α → edgeCopySourcePairData G A B)
    (hinj : Set.InjOn route s) :
    (∑ a ∈ s,
      ((β / 6) * edgeCopySourcePairDataWeight G β J (route a)) / 384) ≤
      ((β * Sharpness.sourcePairSum G β J A B) / 6) / 384 := by
  calc
    (∑ a ∈ s,
      ((β / 6) * edgeCopySourcePairDataWeight G β J (route a)) / 384) =
        (∑ a ∈ s,
          (β / 6) * edgeCopySourcePairDataWeight G β J (route a)) /
          384 := by
      rw [Finset.sum_div]
    _ ≤
        ((β / 6) * Sharpness.sourcePairSum G β J A B) / 384 :=
      div_le_div_of_nonneg_right
        (edgeCopySourcePairDataWeight_finset_sum_route_beta_div_six_le_sourcePairSum_of_injOn
          G hβ J hJ A B s route hinj)
        (by norm_num)
    _ = ((β * Sharpness.sourcePairSum G β J A B) / 6) / 384 := by
      ring

set_option linter.style.longLine false in


theorem
    edgeCopySourcePairDataWeight_finset_attach_sum_route_beta_div_six_div_384_le_sourcePairShare_of_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V)
    {α : Type*} (s : Finset α)
    (route : {a : α // a ∈ s} → edgeCopySourcePairData G A B)
    (hinj : Function.Injective route) :
    (∑ a ∈ s.attach,
        ((β / 6) * edgeCopySourcePairDataWeight G β J (route a)) /
          384) ≤
      ((β * Sharpness.sourcePairSum G β J A B) / 6) / 384 := by
  exact
    edgeCopySourcePairDataWeight_finset_sum_route_beta_div_six_div_384_le_sourcePairShare_of_injOn
      G hβ J hJ A B s.attach route
      (by
        intro a _ha b _hb hab
        exact hinj hab)

set_option linter.style.longLine false in


theorem
    edgeCopySourcePairDataWeight_finset_attach_splitSum_route_beta_div_six_le_sourcePairSum_of_injOn
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V)
    {α Split : Type*} (s : Finset α)
    (split : {a : α // a ∈ s} → Finset Split)
    (route :
      (a : {a : α // a ∈ s}) → Split → edgeCopySourcePairData G A B)
    (hinj :
      Set.InjOn
        (fun p : Sigma (fun _ : {a : α // a ∈ s} => Split) =>
          route p.1 p.2)
        (s.attach.sigma split)) :
    (∑ a ∈ s.attach,
      ∑ i ∈ split a,
        (β / 6) * edgeCopySourcePairDataWeight G β J (route a i)) ≤
      (β / 6) * Sharpness.sourcePairSum G β J A B := by
  calc
    (∑ a ∈ s.attach,
      ∑ i ∈ split a,
        (β / 6) * edgeCopySourcePairDataWeight G β J (route a i)) =
        ∑ p ∈ s.attach.sigma split,
          (β / 6) *
            edgeCopySourcePairDataWeight G β J (route p.1 p.2) := by
      rw [Finset.sum_sigma]
    _ ≤ (β / 6) * Sharpness.sourcePairSum G β J A B :=
      edgeCopySourcePairDataWeight_finset_sum_route_beta_div_six_le_sourcePairSum_of_injOn
        G hβ J hJ A B (s.attach.sigma split)
        (fun p => route p.1 p.2) hinj

set_option linter.style.longLine false in


theorem
    edgeCopySourcePairDataWeight_finset_attach_splitSum_route_beta_div_six_div_384_le_sourcePairShare_of_injOn
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V)
    {α Split : Type*} (s : Finset α)
    (split : {a : α // a ∈ s} → Finset Split)
    (route :
      (a : {a : α // a ∈ s}) → Split → edgeCopySourcePairData G A B)
    (hinj :
      Set.InjOn
        (fun p : Sigma (fun _ : {a : α // a ∈ s} => Split) =>
          route p.1 p.2)
        (s.attach.sigma split)) :
    (∑ a ∈ s.attach,
      ∑ i ∈ split a,
        ((β / 6) * edgeCopySourcePairDataWeight G β J (route a i)) /
          384) ≤
      ((β * Sharpness.sourcePairSum G β J A B) / 6) / 384 := by
  calc
    (∑ a ∈ s.attach,
      ∑ i ∈ split a,
        ((β / 6) * edgeCopySourcePairDataWeight G β J (route a i)) /
          384) =
        ∑ p ∈ s.attach.sigma split,
          ((β / 6) *
            edgeCopySourcePairDataWeight G β J (route p.1 p.2)) /
            384 := by
      rw [Finset.sum_sigma]
    _ ≤ ((β * Sharpness.sourcePairSum G β J A B) / 6) / 384 :=
      edgeCopySourcePairDataWeight_finset_sum_route_beta_div_six_div_384_le_sourcePairShare_of_injOn
        G hβ J hJ A B (s.attach.sigma split)
        (fun p => route p.1 p.2) hinj

set_option linter.style.longLine false in


theorem
    finset_sum_le_sourcePairShare_of_splitDataRoute_beta_div_six_div_384_pointwise
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V)
    {α Split : Type*} (s : Finset α) (F : α → ℝ)
    (split : {a : α // a ∈ s} → Finset Split)
    (route :
      (a : {a : α // a ∈ s}) → Split → edgeCopySourcePairData G A B)
    (hinj :
      Set.InjOn
        (fun p : Sigma (fun _ : {a : α // a ∈ s} => Split) =>
          route p.1 p.2)
        (s.attach.sigma split))
    (hpoint :
      ∀ a : {a : α // a ∈ s},
        F a.1 ≤
          ∑ i ∈ split a,
            ((β / 6) * edgeCopySourcePairDataWeight G β J (route a i)) /
              384) :
    (∑ a ∈ s, F a) ≤
      ((β * Sharpness.sourcePairSum G β J A B) / 6) / 384 := by
  calc
    (∑ a ∈ s, F a) =
        ∑ a ∈ s.attach, F a.1 := by
      exact (Finset.sum_attach s F).symm
    _ ≤
        ∑ a ∈ s.attach,
          ∑ i ∈ split a,
            ((β / 6) * edgeCopySourcePairDataWeight G β J (route a i)) /
              384 := by
      exact Finset.sum_le_sum (fun a _ha => hpoint a)
    _ ≤ ((β * Sharpness.sourcePairSum G β J A B) / 6) / 384 :=
      edgeCopySourcePairDataWeight_finset_attach_splitSum_route_beta_div_six_div_384_le_sourcePairShare_of_injOn
        G hβ J hJ A B s split route hinj

set_option linter.style.longLine false in


theorem edgeCopySourcePairWitnesses_eq_empty_of_left_source_vertex_absent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} {m : ↥G.edgeFinset → ℕ} {x : V}
    (hxA : x ∈ A)
    (habsent :
      ∀ i : Sharpness.FluxEdgeCopy.Copy G m,
        x ∉ Sharpness.FluxEdgeCopy.endsM G m i) :
    edgeCopySourcePairWitnesses G A B m = ∅ := by
  classical
  ext S
  constructor
  · intro hS
    have hsrc := (edgeCopySourcePairWitnesses_mem G A B m S).mp hS
    have hxsrc :
        x ∈ Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m) S := by
      simpa [hsrc.1] using hxA
    have hxnot :
        x ∉ Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m) S :=
      randomCurrent_not_mem_sources_of_forall_not_mem_ends
        (Sharpness.FluxEdgeCopy.endsM G m) S x
        (fun i _hi => habsent i)
    exact False.elim (hxnot hxsrc)
  · intro hS
    simp at hS

set_option linter.style.longLine false in


theorem edgeCopySourcePairSummand_eq_zero_of_left_source_vertex_absent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ)
    {A B : Finset V} {m : ↥G.edgeFinset → ℕ} {x : V}
    (hxA : x ∈ A)
    (habsent :
      ∀ i : Sharpness.FluxEdgeCopy.Copy G m,
        x ∉ Sharpness.FluxEdgeCopy.endsM G m i) :
    edgeCopySourcePairSummand G β J A B m = 0 := by
  rw [edgeCopySourcePairSummand_eq_witness_card_mul_weight]
  rw [edgeCopySourcePairWitnesses_eq_empty_of_left_source_vertex_absent
    G hxA habsent]
  simp

set_option linter.style.longLine false in


theorem fluxEdgeCopy_endsM_not_mem_of_edge_support_absent
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {m : ↥G.edgeFinset → ℕ} {x : V}
    (habsent : ∀ e : ↥G.edgeFinset, m e ≠ 0 → x ∉ e.1) :
    ∀ i : Sharpness.FluxEdgeCopy.Copy G m,
      x ∉ Sharpness.FluxEdgeCopy.endsM G m i := by
  intro i
  have hne : m i.1 ≠ 0 := by
    have hlt : i.2.val < m i.1 := i.2.isLt
    omega
  simpa [Sharpness.FluxEdgeCopy.endsM] using habsent i.1 hne

set_option linter.style.longLine false in


theorem fluxEdgeCopy_endsM_singleEdgeCopies_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e0 : ↥G.edgeFinset) (k : ℕ)
    (i : Sharpness.FluxEdgeCopy.Copy G
      (Function.update (fun _ : ↥G.edgeFinset => 0) e0 k)) :
    Sharpness.FluxEdgeCopy.endsM G
        (Function.update (fun _ : ↥G.edgeFinset => 0) e0 k) i = e0.1 := by
  have hfst : i.1 = e0 := by
    by_contra hne
    have hmzero :
        (Function.update (fun _ : ↥G.edgeFinset => 0) e0 k) i.1 = 0 := by
      simp [hne]
    have hlt : (i.2 : ℕ) <
        (Function.update (fun _ : ↥G.edgeFinset => 0) e0 k) i.1 := i.2.isLt
    omega
  simp [Sharpness.FluxEdgeCopy.endsM, hfst]

set_option linter.style.longLine false in


theorem edgeCopySourceSector_card_mul_weight_eq_sum_sourcePairSummand
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (m : ↥G.edgeFinset → ℕ) :
    ((edgeCopySourceSector G A m).card : ℝ) *
        Sharpness.weight G β J (Sharpness.ofEdgeFun G m) =
      ∑ B : Finset V, edgeCopySourcePairSummand G β J A B m := by
  rw [edgeCopySourceSector_card_eq_sum_sourcePairWitnesses_card]
  rw [Nat.cast_sum]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro B _hB
  rw [edgeCopySourcePairSummand_eq_witness_card_mul_weight]

theorem nat_succ_le_two_pow (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have h1 : k + 2 ≤ 2 * (k + 1) := by omega
      have h2 : 2 * (k + 1) ≤ 2 * 2 ^ k :=
        Nat.mul_le_mul_left 2 ih
      calc
        k + 1 + 1 = k + 2 := by omega
        _ ≤ 2 * (k + 1) := h1
        _ ≤ 2 * 2 ^ k := h2
        _ = 2 ^ (k + 1) := by rw [pow_succ]; omega


end Exact3D
end StatMech
