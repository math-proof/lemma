/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveFoldedGeometry.Part4
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveRouting


namespace StatMech.Ising

noncomputable section

open scoped symmDiff

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaThirdOfThree_spec
    {i j k u v : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hu : u = i ∨ u = j ∨ u = k)
    (hv : v = i ∨ v = j ∨ v = k) (huv : u ≠ v) :
    let l := lpReplicaThirdOfThree i j k u v
    l ≠ u ∧ l ≠ v ∧ (l = i ∨ l = j ∨ l = k) := by
  dsimp only
  rcases hu with rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl <;>
    simp_all [lpReplicaThirdOfThree] <;> aesop


theorem lpReplicaCurrentEdge_toFinset_symmDiff_reflect_eq_seams
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (e : (lpReplicaCurrentGraph G sites).edgeFinset)
    {u v : I} (huv : u ≠ v)
    (hfold : lpReplicaCurrentFoldedEdge G sites e =
      s(Sum.inl (sites u), Sum.inl (sites v))) :
    (Sym2.toFinset (e.1)) ∆
        (Sym2.toFinset (Sym2.map lpReplicaCurrentReflect (e.1))) =
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) u ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) v := by
  have hsuv : sites u ≠ sites v := hsite.ne huv
  induction hval : e.1 using Sym2.inductionOn with
  | _ x y =>
      have hxy : (lpReplicaCurrentGraph G sites).Adj x y := by
        have hmem := e.2
        rw [SimpleGraph.mem_edgeFinset, hval, SimpleGraph.mem_edgeSet] at hmem
        exact hmem
      unfold lpReplicaCurrentFoldedEdge at hfold
      rw [hval, Sym2.map_mk] at hfold
      rcases x with (x | g) <;> rcases y with (y | h)
      · rcases x with x | x <;> rcases y with y | y
        · rw [Sym2.eq_iff] at hfold
          simp only [lpReplicaCurrentFold, Sum.inl.injEq] at hfold
          rcases hfold with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            ext z <;>
            simp [hval, lpMatchingSeamSource, lpReplicaCurrentLeft,
              lpReplicaCurrentRight, lpReplicaCurrentReflect,
              Finset.mem_symmDiff, hsuv, hsuv.symm] <;> aesop
        · rw [lpReplicaCurrentGraph_adj_left_right_iff] at hxy
          obtain ⟨t, htx, hty⟩ := hxy
          have hxy' : x = y := htx.symm.trans hty
          rw [Sym2.eq_iff] at hfold
          simp only [lpReplicaCurrentFold, Sum.inl.injEq] at hfold
          rcases hfold with h | h
          · exact False.elim (hsuv (h.1.symm.trans (hxy'.trans h.2)))
          · exact False.elim (hsuv (h.2.symm.trans (hxy'.symm.trans h.1)))
        · rw [(lpReplicaCurrentGraph G sites).adj_comm,
            lpReplicaCurrentGraph_adj_left_right_iff] at hxy
          obtain ⟨t, hty, htx⟩ := hxy
          have hxy' : x = y := htx.symm.trans hty
          rw [Sym2.eq_iff] at hfold
          simp only [lpReplicaCurrentFold, Sum.inl.injEq] at hfold
          rcases hfold with h | h
          · exact False.elim (hsuv (h.1.symm.trans (hxy'.trans h.2)))
          · exact False.elim (hsuv (h.2.symm.trans (hxy'.symm.trans h.1)))
        · rw [Sym2.eq_iff] at hfold
          simp only [lpReplicaCurrentFold, Sum.inl.injEq] at hfold
          rcases hfold with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            ext z <;>
            simp [hval, lpMatchingSeamSource, lpReplicaCurrentLeft,
              lpReplicaCurrentRight, lpReplicaCurrentReflect,
              Finset.mem_symmDiff, hsuv, hsuv.symm] <;> aesop
      · rcases x with x | x <;> cases h <;>
          rw [Sym2.eq_iff] at hfold <;>
          simp only [lpReplicaCurrentFold, Sum.inl.injEq,
            Sum.inr.injEq, reduceCtorEq, and_false, false_and,
            or_self] at hfold
      · cases g <;> rcases y with y | y <;>
          rw [Sym2.eq_iff] at hfold <;>
          simp only [lpReplicaCurrentFold, Sum.inl.injEq,
            Sum.inr.injEq, reduceCtorEq, and_false, false_and,
            or_self] at hfold
      · cases g <;> cases h <;>
          rw [Sym2.eq_iff] at hfold <;>
          simp only [lpReplicaCurrentFold, Sum.inl.injEq,
            Sum.inr.injEq, reduceCtorEq, and_false, false_and,
            or_self] at hfold

set_option maxHeartbeats 1200000 in


theorem lpReplicaAggregateUnmarkedSaturatedSourceRankFive_exists_strictPhysicalRoute
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    let a := z.toAggregate G sites q
    let k := lpReplicaAggregateDecoratedSourceSelectedSeam
      G sites hsite q a
    ∃ c d : StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1,
      c.1.1 = lpReplicaCurrentSeamEdge sites k ∧
        d ∈ Finset.univ \ {c} ∧
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∉
          StatMech.Sharpness.FluxEdgeCopy.endsM
            (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1 d ∧
        (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∉
          StatMech.Sharpness.FluxEdgeCopy.endsM
            (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1 d ∧
        ¬ (lpReplicaCurrentFoldedEdge G sites d.1).IsDiag := by
  classical
  dsimp only
  let a := z.toAggregate G sites q
  let k := lpReplicaAggregateDecoratedSourceSelectedSeam
    G sites hsite q a
  have hpm :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_selectedSeam_perfectMatching
      G sites hsite q hcard z
  change ∃ c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1,
    c.1.1 = lpReplicaCurrentSeamEdge sites k ∧
      let K := Finset.univ \ {c}
      let E := StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1
      K.card = 4 ∧
        StatMech.Sharpness.RandomCurrent.sources E K =
          lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k ∧
        K.biUnion (fun e => (E e).toFinset) =
          lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k ∧
        ∀ x ∈ lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k,
          ∃! e, e ∈ K ∧ x ∈ (E e).toFinset at hpm
  obtain ⟨c, hc, hKcard, hsources, hsupport, hunique⟩ := hpm
  let K := Finset.univ \ {c}
  have hij : a.1 ≠ a.2.1 :=
    lpReplicaAggregateDecoratedSource_indices_ne G sites q a
  have hkunmarked :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_selectedSeam_unmarked
      G sites hsite q hcard z
  have hik : a.1 ≠ k := Ne.symm hkunmarked.1
  have hjk : a.2.1 ≠ k := Ne.symm hkunmarked.2
  have hunmarked :=
    LPReplicaOffdiagDecoratedSource.isUnmarkedSaturatedRankFive_of_mem_complement
      G sites hsite hij q hcard z.2.2.2.1 z.2.2.2.2
  obtain ⟨d, hdK, hd0, hd1, hddiag⟩ :=
    lpReplica_fourCopyTripleMatching_exists_strictPhysicalRoute
      G sites hsite hij hik hjk a.2.2.2.1.1.1 K hKcard hsupport hunique
        (fun e _ => hunmarked.2.1 e) (fun e _ => hunmarked.2.2 e)
  exact ⟨c, d, hc, hdK, hd0, hd1, hddiag⟩

set_option maxHeartbeats 1200000 in


theorem lpReplicaAggregateUnmarkedSaturatedSourceRankFive_exists_labeledRoute
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    let a := z.toAggregate G sites q
    let k := lpReplicaAggregateDecoratedSourceSelectedSeam
      G sites hsite q a
    ∃ c d : StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1,
      ∃ u v,
      c.1.1 = lpReplicaCurrentSeamEdge sites k ∧
        d ∈ Finset.univ \ {c} ∧
        (u = a.1 ∨ u = a.2.1 ∨ u = k) ∧
        (v = a.1 ∨ v = a.2.1 ∨ v = k) ∧
        u ≠ v ∧
        lpReplicaCurrentFoldedEdge G sites d.1 =
          s(Sum.inl (sites u), Sum.inl (sites v)) ∧
        let l := lpReplicaThirdOfThree a.1 a.2.1 k u v
        l ≠ u ∧ l ≠ v ∧ (l = a.1 ∨ l = a.2.1 ∨ l = k) := by
  classical
  dsimp only
  let a := z.toAggregate G sites q
  let k := lpReplicaAggregateDecoratedSourceSelectedSeam
    G sites hsite q a
  have hroute :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_exists_strictPhysicalRoute
      G sites hsite q hcard z
  change ∃ c d : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1,
    c.1.1 = lpReplicaCurrentSeamEdge sites k ∧
      d ∈ Finset.univ \ {c} ∧
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∉
        StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1 d ∧
      (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∉
        StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1 d ∧
      ¬ (lpReplicaCurrentFoldedEdge G sites d.1).IsDiag at hroute
  obtain ⟨c, d, hc, hdK, hd0, hd1, hddiag⟩ := hroute
  let K := Finset.univ \ {c}
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1
  have hij : a.1 ≠ a.2.1 :=
    lpReplicaAggregateDecoratedSource_indices_ne G sites q a
  have hkunmarked :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_selectedSeam_unmarked
      G sites hsite q hcard z
  have hik : a.1 ≠ k := Ne.symm hkunmarked.1
  have hjk : a.2.1 ≠ k := Ne.symm hkunmarked.2
  have hKcard : K.card = 4 :=
    lpReplicaOffdiagDecoratedSource_card_erase_copy_rankFive
      G sites q hcard a.2.2.2 c
  have hsources : StatMech.Sharpness.RandomCurrent.sources E K =
      lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k :=
    lpReplicaOffdiagDecoratedSource_sources_erase_seamCopy
      G sites q a.2.2.2 c hc
  have htight :
      (StatMech.Sharpness.RandomCurrent.sources E K).card = 2 * K.card := by
    rw [hsources, card_lpReplicaTripleSeamGhostSource sites hsite
      hij hik hjk, hKcard]
  have hsupport : K.biUnion (fun e => (E e).toFinset) =
      lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k :=
    (randomCurrent_endpointSupport_eq_sources_of_card_eq_two_mul
      E K htight).trans hsources
  obtain ⟨u, v, hu, hv, huv, hfold⟩ :=
    lpReplica_strictPhysicalRoute_folded_labels G sites hsite
      hij hik hjk a.2.2.2.1.1.1 K hsupport d hdK hd0 hd1 hddiag
  have hl := lpReplicaThirdOfThree_spec hij hik hjk hu hv huv
  exact ⟨c, d, u, v, hc, hdK, hu, hv, huv, hfold, hl⟩

end
end StatMech.Ising
