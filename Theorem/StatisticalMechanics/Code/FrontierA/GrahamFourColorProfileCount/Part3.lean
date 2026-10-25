/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorProfileCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamLemmaOneFourColor
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Def.StatisticalMechanics.Code.FrontierA.GrahamFourColorProfileCount.Part2
open Finset
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness.FluxEdgeCopy


section SigmaPi

variable {E : Type*} [Fintype E] [DecidableEq E]
  {gamma : E -> Type*} [forall e, Fintype (gamma e)]
  [forall e, DecidableEq (gamma e)]

theorem grahamFourColor_pi_profile_count (K1 K2 K3 : E -> Nat) :
    #((Finset.univ :
        Finset (GrahamFourColoring (Sigma fun e : E => gamma e))).filter
      (fun c => c.IsPartition Finset.univ /\
        grahamFourColorProfile c = (K1, K2, K3))) =
      ∏ e : E,
        (Fintype.card (gamma e)).choose (K1 e) *
          (Fintype.card (gamma e) - K1 e).choose (K2 e) *
          (Fintype.card (gamma e) - K1 e - K2 e).choose (K3 e) := by
  rw [show ((Finset.univ :
        Finset (GrahamFourColoring (Sigma fun e : E => gamma e))).filter
      (fun c => c.IsPartition Finset.univ /\
        grahamFourColorProfile c = (K1, K2, K3))) =
      (Fintype.piFinset (fun e =>
        (Finset.univ : Finset (GrahamFourColoring (gamma e))).filter
          (fun c => c.IsPartition Finset.univ /\
            #c.color1 = K1 e /\ #c.color2 = K2 e /\
              #c.color3 = K3 e))).image grahamFourColorSigmaEquivPi.symm by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hpart, hprof⟩
      refine ⟨grahamFourColorSigmaEquivPi c, ?_, ?_⟩
      · intro e
        have h1 := congrFun (congrArg Prod.fst hprof) e
        have h2 := congrFun (congrArg (fun p => p.2.1) hprof) e
        have h3 := congrFun (congrArg (fun p => p.2.2) hprof) e
        refine ⟨(grahamFourColor_partition_fiberwise c).mp hpart e,
          ?_, ?_, ?_⟩
        · change #(sigmaFinsetEquivPi c.color1 e) = K1 e
          simpa [grahamFourColorProfile] using h1
        · change #(sigmaFinsetEquivPi c.color2 e) = K2 e
          simpa [grahamFourColorProfile] using h2
        · change #(sigmaFinsetEquivPi c.color3 e) = K3 e
          simpa [grahamFourColorProfile] using h3
      · rw [Equiv.symm_apply_apply]
    · rintro ⟨f, hf, hfc⟩
      subst hfc
      have happ : grahamFourColorSigmaEquivPi
          (grahamFourColorSigmaEquivPi.symm f) = f :=
        Equiv.apply_symm_apply grahamFourColorSigmaEquivPi f
      have hpart : forall e,
          (grahamFourColorSigmaEquivPi
            (grahamFourColorSigmaEquivPi.symm f) e).IsPartition Finset.univ := by
        intro e
        rw [congrFun happ e]
        exact (hf e).1
      refine ⟨(grahamFourColor_partition_fiberwise _).mpr hpart, ?_⟩
      apply Prod.ext
      · funext e
        change #(grahamFourColorSigmaEquivPi
          (grahamFourColorSigmaEquivPi.symm f) e).color1 = K1 e
        rw [congrFun happ e]
        exact (hf e).2.1
      · apply Prod.ext
        · funext e
          change #(grahamFourColorSigmaEquivPi
            (grahamFourColorSigmaEquivPi.symm f) e).color2 = K2 e
          rw [congrFun happ e]
          exact (hf e).2.2.1
        · funext e
          change #(grahamFourColorSigmaEquivPi
            (grahamFourColorSigmaEquivPi.symm f) e).color3 = K3 e
          rw [congrFun happ e]
          exact (hf e).2.2.2]
  rw [Finset.card_image_of_injective _
    grahamFourColorSigmaEquivPi.symm.injective, Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro e he
  exact grahamFourColor_perFiber_count (gamma e)
    (Fintype.card (gamma e)) (K1 e) (K2 e) (K3 e) rfl

end SigmaPi

section EdgeCopies

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem grahamFourColor_edgecopy_profile_count
    (total a b c : G.edgeFinset -> Nat) :
    #((grahamFourColorings
        (Finset.univ : Finset (Copy G total))).filter (fun q =>
      profileFlux G total q.color1 = a /\
        profileFlux G total q.color2 = b /\
        profileFlux G total q.color3 = c)) =
      ∏ e : G.edgeFinset,
        (total e).choose (a e) *
          (total e - a e).choose (b e) *
          (total e - a e - b e).choose (c e) := by
  simpa only [grahamFourColorings, Finset.filter_filter,
      grahamFourColorProfile, profileFlux,
      sigmaFinsetEquivPi_apply_card, Fintype.card_fin,
      and_assoc, Prod.mk.injEq] using
    (grahamFourColor_pi_profile_count
      (gamma := fun e : G.edgeFinset => Fin (total e)) a b c)


theorem grahamFourColor_profile_sum_le
    (total : G.edgeFinset -> Nat)
    (q : GrahamFourColoring (Copy G total))
    (hq : q.IsPartition Finset.univ) :
    forall e, profileFlux G total q.color1 e +
        profileFlux G total q.color2 e +
        profileFlux G total q.color3 e <= total e := by
  intro e
  let A := q.color1.filter (fun i : Copy G total => i.1 = e)
  let B := q.color2.filter (fun i : Copy G total => i.1 = e)
  let C := q.color3.filter (fun i : Copy G total => i.1 = e)
  have hAB : Disjoint A B := by
    exact Finset.disjoint_filter_filter hq.2.2.2.1
  have hAC : Disjoint A C := by
    exact Finset.disjoint_filter_filter hq.2.2.2.2.1
  have hBC : Disjoint B C := by
    exact Finset.disjoint_filter_filter hq.2.2.2.2.2
  have hABC : Disjoint (A ∪ B) C :=
    Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩
  have hsub : (A ∪ B) ∪ C ⊆
      (Finset.univ : Finset (Copy G total)).filter (fun i => i.1 = e) := by
    intro i hi
    simp only [Finset.mem_union] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hi with (hi | hi) | hi
    · exact (Finset.mem_filter.mp hi).2
    · exact (Finset.mem_filter.mp hi).2
    · exact (Finset.mem_filter.mp hi).2
  change #A + #B + #C <= total e
  rw [← Finset.card_union_of_disjoint hAB,
    ← Finset.card_union_of_disjoint hABC,
    ← fiber_card G total e]
  exact Finset.card_le_card hsub

theorem graham_profileFlux_union_disjoint
    (total : G.edgeFinset -> Nat) (S T : Finset (Copy G total))
    (hST : Disjoint S T) :
    profileFlux G total (S ∪ T) = fun e =>
      profileFlux G total S e + profileFlux G total T e := by
  funext e
  unfold profileFlux
  have hd : Disjoint
      (S.filter (fun i : Copy G total => i.1 = e))
      (T.filter (fun i : Copy G total => i.1 = e)) :=
    Finset.disjoint_filter_filter hST
  rw [← Finset.card_union_of_disjoint hd]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_union]
  tauto


theorem grahamFourColor_profile_color4
    (total : G.edgeFinset -> Nat)
    (q : GrahamFourColoring (Copy G total))
    (hq : q.IsPartition Finset.univ) :
    profileFlux G total (q.color4 Finset.univ) =
      fun e => total e - profileFlux G total q.color1 e -
        profileFlux G total q.color2 e -
        profileFlux G total q.color3 e := by
  unfold GrahamFourColoring.color4
  rw [profileFlux_compl]
  have h12 := graham_profileFlux_union_disjoint G total
    q.color1 q.color2 hq.2.2.2.1
  have h123 : Disjoint (q.color1 ∪ q.color2) q.color3 :=
    Finset.disjoint_union_left.mpr ⟨hq.2.2.2.2.1, hq.2.2.2.2.2⟩
  rw [graham_profileFlux_union_disjoint G total
    (q.color1 ∪ q.color2) q.color3 h123, h12]
  funext e
  have hle := grahamFourColor_profile_sum_le G total q hq e
  simp only
  omega

end EdgeCopies
end StatMech.FrontierA
