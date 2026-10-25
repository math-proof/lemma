/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorProfileCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamLemmaOneFourColor
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
open Finset
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness.FluxEdgeCopy


theorem grahamFourColor_perFiber_count
    (alpha : Type*) [Fintype alpha] [DecidableEq alpha]
    (n k1 k2 k3 : Nat) (hn : Fintype.card alpha = n) :
    #((Finset.univ : Finset (GrahamFourColoring alpha)).filter (fun c =>
        c.IsPartition Finset.univ /\
          #c.color1 = k1 /\ #c.color2 = k2 /\ #c.color3 = k3)) =
      n.choose k1 * (n - k1).choose k2 *
        (n - k1 - k2).choose k3 := by
  let S := (Finset.univ : Finset (GrahamFourColoring alpha)).filter (fun c =>
    c.IsPartition Finset.univ /\
      #c.color1 = k1 /\ #c.color2 = k2 /\ #c.color3 = k3)
  let Aset := (Finset.univ : Finset alpha).powersetCard k1
  rw [show ((Finset.univ : Finset (GrahamFourColoring alpha)).filter (fun c =>
      c.IsPartition Finset.univ /\
        #c.color1 = k1 /\ #c.color2 = k2 /\ #c.color3 = k3)) = S by rfl]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun c : GrahamFourColoring alpha => c.color1) (t := Aset)
    (by
      intro c hc
      simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
        true_and] at hc
      simp only [Aset, Finset.mem_coe, Finset.mem_powersetCard]
      exact ⟨subset_univ _, hc.2.1⟩)]
  have hA : ∀ A, A ∈ Aset →
      #(S.filter (fun c => c.color1 = A)) =
        (n - k1).choose k2 * (n - k1 - k2).choose k3 := by
    intro A hAmem
    have hAdata : A ⊆ (Finset.univ : Finset alpha) /\ #A = k1 := by
      simpa [Aset] using hAmem
    let Bset := (Finset.univ \ A).powersetCard k2
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun c : GrahamFourColoring alpha => c.color2) (t := Bset)
      (by
        intro c hc
        simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
          true_and] at hc
        rcases hc with ⟨⟨hpart, _, hc2, _⟩, hcA⟩
        subst hcA
        simp only [Bset, Finset.mem_coe, Finset.mem_powersetCard]
        refine ⟨?_, hc2⟩
        intro x hx
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact fun hxA =>
          (Finset.disjoint_left.mp hpart.2.2.2.1) hxA hx)]
    have hB : ∀ B, B ∈ Bset →
        #((S.filter (fun c => c.color1 = A)).filter
            (fun c => c.color2 = B)) =
          (n - k1 - k2).choose k3 := by
      intro B hBmem
      have hBdata : B ⊆ Finset.univ \ A /\ #B = k2 := by
        simpa [Bset] using hBmem
      let Cset := (Finset.univ \ (A ∪ B)).powersetCard k3
      rw [show ((S.filter (fun c => c.color1 = A)).filter
            (fun c => c.color2 = B)) =
          Cset.image (fun C =>
            ({ color1 := A, color2 := B, color3 := C } :
              GrahamFourColoring alpha)) by
        ext c
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_image, Cset, Finset.mem_powersetCard]
        constructor
        · rintro ⟨⟨⟨hpart, hc1, hc2, hc3⟩, hca⟩, hcb⟩
          subst hca
          subst hcb
          refine ⟨c.color3, ⟨?_, hc3⟩, ?_⟩
          · intro x hx
            simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
              Finset.mem_union]
            exact fun hxAB => hxAB.elim
              (fun hxA =>
                (Finset.disjoint_left.mp hpart.2.2.2.2.1) hxA hx)
              (fun hxB =>
                (Finset.disjoint_left.mp hpart.2.2.2.2.2) hxB hx)
          · cases c
            rfl
        · rintro ⟨C, ⟨hCsub, hCcard⟩, rfl⟩
          have hAB : Disjoint A B := by
            rw [Finset.disjoint_left]
            intro x hxA hxB
            exact (Finset.mem_sdiff.mp (hBdata.1 hxB)).2 hxA
          have hAC : Disjoint A C := by
            rw [Finset.disjoint_left]
            intro x hxA hxC
            exact (Finset.mem_sdiff.mp (hCsub hxC)).2
              (Finset.mem_union_left B hxA)
          have hBC : Disjoint B C := by
            rw [Finset.disjoint_left]
            intro x hxB hxC
            exact (Finset.mem_sdiff.mp (hCsub hxC)).2
              (Finset.mem_union_right A hxB)
          exact ⟨⟨⟨⟨subset_univ _, subset_univ _, subset_univ _, hAB, hAC,
            hBC⟩, hAdata.2, hBdata.2, hCcard⟩, rfl⟩, rfl⟩]
      rw [Finset.card_image_of_injective]
      · rw [Finset.card_powersetCard]
        have hAB : Disjoint A B := by
          rw [Finset.disjoint_left]
          intro x hxA hxB
          exact (Finset.mem_sdiff.mp (hBdata.1 hxB)).2 hxA
        congr 1
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hn,
          Finset.card_union_of_disjoint hAB]
        omega
      · intro C D hCD
        exact congrArg GrahamFourColoring.color3 hCD
    rw [Finset.sum_congr rfl hB, Finset.sum_const, Finset.card_powersetCard]
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hn, hAdata.2]
    simp only [nsmul_eq_mul]
    simp
  rw [Finset.sum_congr rfl hA, Finset.sum_const, Finset.card_powersetCard]
  rw [Finset.card_univ, hn]
  simp only [nsmul_eq_mul, Nat.mul_assoc]
  simp

section SigmaPi

variable {E : Type*} [Fintype E] [DecidableEq E]
  {gamma : E -> Type*} [forall e, Fintype (gamma e)]
  [forall e, DecidableEq (gamma e)]

theorem graham_mem_sigmaFinsetEquivPi
    (S : Finset (Sigma fun e : E => gamma e)) (e : E) (x : gamma e) :
    x ∈ sigmaFinsetEquivPi S e <->
      (Sigma.mk e x : Sigma fun e : E => gamma e) ∈ S := by
  rw [show sigmaFinsetEquivPi S e =
      (Finset.univ : Finset (gamma e)).filter (fun x =>
        (Sigma.mk e x : Sigma fun e : E => gamma e) ∈ S) from rfl]
  simp


end SigmaPi
end StatMech.FrontierA
