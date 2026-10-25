/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidateTargets.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidates.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder.Part3
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictInvariant
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveOrderedPairSwap.Part4
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidateTargets


namespace StatMech.Ising

noncomputable section

open scoped symmDiff

open StatMech.Sharpness.FluxEdgeCopy

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaCurrentFoldedEdge_isDiag_of_mem_orbitFixed
    (G : SimpleGraph V) (sites : I -> V)
    (e : (lpReplicaCurrentGraph G sites).edgeFinset)
    (hfixed : e ∈ lpReplicaCurrentEdgeOrbitFixed G sites) :
    (lpReplicaCurrentFoldedEdge G sites e).IsDiag := by
  have hreflect : lpReplicaCurrentEdgeReflect G sites e = e :=
    ((mem_lpReplicaCurrentEdgeOrbitFixed G sites e).mp hfixed).symm
  have hval := congrArg Subtype.val hreflect
  rw [lpReplicaCurrentEdgeReflect_val] at hval
  induction he : e.1 using Sym2.inductionOn with
  | _ x y =>
      rw [he, Sym2.map_mk, Sym2.eq_iff] at hval
      have hnofix : ∀ z : LPReplicaCurrentVertex V,
          lpReplicaCurrentReflect z ≠ z := by
        intro z
        rcases z with (z | b)
        · rcases z with z | z <;> simp
        · cases b <;> simp
      rcases hval with hsame | hswap
      · exact False.elim (hnofix x hsame.1)
      · unfold lpReplicaCurrentFoldedEdge
        rw [he, Sym2.map_mk, Sym2.mk_isDiag_iff]
        calc
          lpReplicaCurrentFold x =
              lpReplicaCurrentFold (lpReplicaCurrentReflect x) :=
            (lpReplicaCurrentFold_reflect x).symm
          _ = lpReplicaCurrentFold y := congrArg lpReplicaCurrentFold hswap.1


theorem lpReplicaProfileCopyEquivCommonSlot_eq_inr_of_folded_not_diag
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (d : Copy (lpReplicaCurrentGraph G sites) m)
    (hdiag : ¬ (lpReplicaCurrentFoldedEdge G sites d.1).IsDiag) :
    ∃ x, lpReplicaProfileCopyEquivCommonSlot G sites q m hm L d =
      Sum.inr x := by
  let E := lpReplicaProfileCopyEquivCommonSlot G sites q m hm L
  rcases hE : E d with fixed | strict
  · exfalso
    apply hdiag
    have hfold := lpReplicaOrbitFoldedSlotEnds_copy
      G sites q m hm L d
    rw [hE] at hfold
    rw [← hfold]
    exact lpReplicaCurrentFoldedEdge_isDiag_of_mem_orbitFixed
      G sites fixed.1.1 fixed.1.2
  · exact ⟨strict, rfl⟩


theorem lpReplicaOrbitFourColorSlotReflectRowToggle_strictSingleton_injective
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaOrbitFourColorSlotState G sites q)
    (row : Finset (LPReplicaOrbitCommonSlot G sites q))
    {d e : LPReplicaOrbitCommonSlot G sites q}
    (hd : ∃ x, d = Sum.inr x) (he : ∃ x, e = Sum.inr x)
    (hstate :
      lpReplicaOrbitFourColorSlotReflectRowToggle G sites q {d} row s =
        lpReplicaOrbitFourColorSlotReflectRowToggle G sites q {e} row s) :
    d = e := by
  rcases hd with ⟨d, rfl⟩
  rcases he with ⟨e, rfl⟩
  have hallocation := congrArg
    (fun t : LPReplicaOrbitFourColorSlotState G sites q =>
      t.allocation d.1) hstate
  change s.allocation d.1 ∆
      lpReplicaOrbitFourColorSelectedStrictSlots G sites q {Sum.inr d} d.1 =
    s.allocation d.1 ∆
      lpReplicaOrbitFourColorSelectedStrictSlots G sites q {Sum.inr e} d.1
      at hallocation
  have hselected := symmDiff_right_injective (s.allocation d.1) hallocation
  have hdmem : d.2 ∈
      lpReplicaOrbitFourColorSelectedStrictSlots
        G sites q {Sum.inr d} d.1 := by
    simp only [lpReplicaOrbitFourColorSelectedStrictSlots,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact Finset.mem_singleton.mpr rfl
  rw [hselected] at hdmem
  have hmemSlot : (Sum.inr d : LPReplicaOrbitCommonSlot G sites q) ∈
      ({Sum.inr e} : Finset (LPReplicaOrbitCommonSlot G sites q)) := by
    simpa [lpReplicaOrbitFourColorSelectedStrictSlots] using hdmem
  exact Finset.mem_singleton.mp hmemSlot

@[simp] theorem lpReplicaOrbitCommonSlotsOfCopies_singleton
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (c : Copy (lpReplicaCurrentGraph G sites) m) :
    lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L {c} =
      {lpReplicaProfileCopyEquivCommonSlot G sites q m hm L c} := by
  classical
  simp [lpReplicaOrbitCommonSlotsOfCopies]


theorem lpReplicaAggregateDecoratedSource_indices_eq_of_pairCode_orientation_eq
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z w : LPReplicaAggregateDecoratedSource G sites q)
    (hpair : s(z.1, z.2.1) = s(w.1, w.2.1))
    (horientation :
      (lpReplicaAggregateDecoratedSourcePairCode G sites q z).1 =
        (lpReplicaAggregateDecoratedSourcePairCode G sites q w).1) :
    z.1 = w.1 ∧ z.2.1 = w.2.1 := by
  classical
  rw [Sym2.eq_iff] at hpair
  rcases hpair with hpair | hpair
  · exact hpair
  · have hzNe : z.1 ≠ z.2.1 :=
      lpReplicaAggregateDecoratedSource_indices_ne G sites q z
    have hrankNe : ((Fintype.equivFin I) z.1).val ≠
        ((Fintype.equivFin I) z.2.1).val := by
      intro h
      apply hzNe
      apply (Fintype.equivFin I).injective
      exact Fin.ext h
    by_cases hz : LPReplicaAggregateDecoratedSource.IsCanonicalOrderedPair
        G sites q z
    · by_cases hw : LPReplicaAggregateDecoratedSource.IsCanonicalOrderedPair
          G sites q w
      · unfold LPReplicaAggregateDecoratedSource.IsCanonicalOrderedPair at hz hw
        rw [← hpair.1, ← hpair.2] at hw
        omega
      · simp [lpReplicaAggregateDecoratedSourcePairCode, hz, hw]
          at horientation
    · by_cases hw : LPReplicaAggregateDecoratedSource.IsCanonicalOrderedPair
          G sites q w
      · simp [lpReplicaAggregateDecoratedSourcePairCode, hz, hw]
          at horientation
      · unfold LPReplicaAggregateDecoratedSource.IsCanonicalOrderedPair at hz hw
        rw [← hpair.1, ← hpair.2] at hw
        omega


theorem lpReplicaStrictRoute_markedPair_eq_of_third_eq_of_routePair_eq
    {i j k u v i' j' u' v' : I}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hij' : i' ≠ j') (hik' : i' ≠ k) (hjk' : j' ≠ k)
    (hu : u = i ∨ u = j ∨ u = k)
    (hv : v = i ∨ v = j ∨ v = k) (huv : u ≠ v)
    (hu' : u' = i' ∨ u' = j' ∨ u' = k)
    (hv' : v' = i' ∨ v' = j' ∨ v' = k) (huv' : u' ≠ v')
    (hthird : lpReplicaThirdOfThree i j k u v =
      lpReplicaThirdOfThree i' j' k u' v')
    (hroute : s(u, v) = s(u', v')) :
    s(i, j) = s(i', j') := by
  rcases hu with rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl <;>
    rcases hu' with rfl | rfl | rfl <;>
    rcases hv' with rfl | rfl | rfl <;>
    simp_all [lpReplicaThirdOfThree] <;> aesop


theorem lpReplica_sitePair_eq_of_currentPhysicalPair_eq
    (sites : I -> V) (hsite : Function.Injective sites)
    {u v u' v' : I}
    (hpair : s((Sum.inl (sites u) : V ⊕ Unit), Sum.inl (sites v)) =
      s((Sum.inl (sites u') : V ⊕ Unit), Sum.inl (sites v'))) :
    s(u, v) = s(u', v') := by
  rw [Sym2.eq_iff] at hpair ⊢
  rcases hpair with hpair | hpair
  · exact Or.inl ⟨hsite (Sum.inl.inj hpair.1),
      hsite (Sum.inl.inj hpair.2)⟩
  · exact Or.inr ⟨hsite (Sum.inl.inj hpair.1),
      hsite (Sum.inl.inj hpair.2)⟩


end
end StatMech.Ising
