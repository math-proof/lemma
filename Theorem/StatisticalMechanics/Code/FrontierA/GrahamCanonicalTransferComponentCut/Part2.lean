/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferAmbientQuadrangle.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedComponent.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem connK_edgeComponent_of_conn_cut
    (ends : I -> Sym2 W) (K : Finset I) (u x : W)
    (hux : connK ends K u x) :
    connK ends (edgeComponent ends K u) u x := by
  classical
  induction hux with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a b _ hstep ih =>
      obtain ⟨i, hiK, ha, hb, hab⟩ := hstep
      have hua : connK ends K u a := by
        apply connK_mono _ ih
        intro e he
        rw [edgeComponent, Finset.mem_filter] at he
        exact he.1
      exact ih.tail ⟨i,
        mem_edgeComponent_of_reachable_endpoint hua hiK ha,
        ha, hb, hab⟩


theorem canonicalTransferUnion_twoRootSpanning
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (c : ↑m -> Fin 4) :
    TwoRootSpanning ends (canonicalTransferUnion ends m k zero c)
      k zero := by
  classical
  intro i hi x hx
  have hunion := canonicalTransfers_union
    (ends := ends) (m := m) (k := k) (zero := zero) (c := c)
  change i ∈ canonicalMiddleTransfer ends m c k zero ∪
    canonicalOuterTransfer ends m c k zero at hi
  rw [hunion, Finset.mem_union] at hi
  have hzeroSub : edgeComponent ends (rowClass m c 0) zero ⊆
      canonicalTransferUnion ends m k zero c := by
    rw [canonicalTransferUnion, hunion]
    exact Finset.subset_union_left
  have hkSub : edgeComponent ends (rowClass m c 1) k ⊆
      canonicalTransferUnion ends m k zero c := by
    rw [canonicalTransferUnion, hunion]
    exact Finset.subset_union_right
  rcases hi with hi0 | hi1
  · right
    rw [edgeComponent, Finset.mem_filter] at hi0
    exact connK_mono hzeroSub
      (connK_edgeComponent_of_conn_cut ends _ zero x (hi0.2 x hx))
  · left
    rw [edgeComponent, Finset.mem_filter] at hi1
    exact connK_mono hkSub
      (connK_edgeComponent_of_conn_cut ends _ k x (hi1.2 x hx))


theorem exists_twoRootSpanning_crossing_edge_of_mem_sdiff_edgeComponent
    (ends : I -> Sym2 W) (K T : Finset I) (k zero : W)
    (hkzero : connK ends K k zero)
    (hT : TwoRootSpanning ends T k zero)
    {i : I} (hi : i ∈ K \ edgeComponent ends K zero)
    (hiT : i ∈ T) :
    ∃ e, e ∈ T \ K ∧
      ∃ a b, a ∈ ends e ∧ b ∈ ends e ∧
        a ∉ StatMech.FrontierA.grahamComponentComplement ends K zero ∧
        b ∈ StatMech.FrontierA.grahamComponentComplement ends K zero := by
  let S := StatMech.FrontierA.grahamComponentComplement ends K zero
  let x := (ends i).out.1
  have hxend : x ∈ ends i := Sym2.out_fst_mem (ends i)
  have hxS : x ∈ S := by
    exact ((mem_sdiff_edgeComponent_iff_edgeInside_componentComplement
      ends K zero).mp hi).2 x hxend
  have hcross : NoCrossingK ends K S := by
    exact StatMech.FrontierA.grahamComponentComplement_noCrossing
      ends K zero
  have hzeroS : zero ∉ S :=
    StatMech.FrontierA.grahamComponentComplement_not_mem ends K zero
  have hkS : k ∉ S :=
    connK_not_mem_of_noCrossing hcross hzeroS
      (connK_symm ends K hkzero)
  rcases hT i hiT x hxend with hkx | hzerox
  · exact exists_crossing_edge_mem_sdiff_of_connK
      hcross hkS hxS hkx
  · exact exists_crossing_edge_mem_sdiff_of_connK
      hcross hzeroS hxS hzerox


theorem twoRootSpanning_union
    {ends : I -> Sym2 W} {A B : Finset I} {u v : W}
    (hA : TwoRootSpanning ends A u v)
    (hB : TwoRootSpanning ends B u v) :
    TwoRootSpanning ends (A ∪ B) u v := by
  intro i hi x hx
  rcases Finset.mem_union.mp hi with hiA | hiB
  · rcases hA i hiA x hx with h | h
    · exact Or.inl (connK_mono Finset.subset_union_left h)
    · exact Or.inr (connK_mono Finset.subset_union_left h)
  · rcases hB i hiB x hx with h | h
    · exact Or.inl (connK_mono Finset.subset_union_right h)
    · exact Or.inr (connK_mono Finset.subset_union_right h)


theorem rootSpanning_union_of_conn_of_twoRootSpanning
    {ends : I -> Sym2 W} {K S : Finset I} {u v : W}
    (hK : RootSpanning ends K u)
    (huv : connK ends K u v)
    (hS : TwoRootSpanning ends S u v) :
    RootSpanning ends (K ∪ S) u := by
  intro i hi x hx
  rcases Finset.mem_union.mp hi with hiK | hiS
  · exact connK_mono Finset.subset_union_left (hK i hiK x hx)
  · rcases hS i hiS x hx with hux | hvx
    · exact connK_mono Finset.subset_union_right hux
    · exact (connK_mono Finset.subset_union_left huv).trans
        (connK_mono Finset.subset_union_right hvx)


theorem edgeComponent_rootSpanning
    (ends : I -> Sym2 W) (K : Finset I) (u : W) :
    RootSpanning ends (edgeComponent ends K u) u := by
  classical
  intro i hi x hx
  rw [edgeComponent, Finset.mem_filter] at hi
  exact connK_edgeComponent_of_conn_cut ends K u x (hi.2 x hx)


theorem subset_edgeComponent_of_subset_of_rootSpanning_union
    (ends : I -> Sym2 W) (K D : Finset I) (u : W)
    (hDK : D ⊆ K)
    (hroot : RootSpanning ends (edgeComponent ends K u ∪ D) u) :
    D ⊆ edgeComponent ends K u := by
  classical
  have hcompK : edgeComponent ends K u ⊆ K := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hunionK : edgeComponent ends K u ∪ D ⊆ K :=
    Finset.union_subset hcompK hDK
  intro i hiD
  rw [edgeComponent, Finset.mem_filter]
  refine ⟨hDK hiD, ?_⟩
  intro x hx
  exact connK_mono hunionK
    (hroot i (Finset.mem_union_right _ hiD) x hx)


theorem rootSpanning_union_of_edgeComponents_meet
    (ends : I -> Sym2 W) (E D : Finset I) (u : W)
    (hE : RootSpanning ends E u)
    (hmeet : ∀ i ∈ D, ∀ x ∈ ends i,
      ∃ e ∈ D ∩ E, ∃ y ∈ ends e, connK ends D x y) :
    RootSpanning ends (E ∪ D) u := by
  intro i hi x hx
  rcases Finset.mem_union.mp hi with hiE | hiD
  · exact connK_mono Finset.subset_union_left (hE i hiE x hx)
  · obtain ⟨e, he, y, hy, hxy⟩ := hmeet i hiD x hx
    have heE : e ∈ E := (Finset.mem_inter.mp he).2
    have huy : connK ends E u y := hE e heE y hy
    exact (connK_mono Finset.subset_union_left huy).trans
      (connK_mono Finset.subset_union_right
        (connK_symm ends D hxy))


theorem subset_edgeComponent_of_subset_of_edgeComponents_meet
    (ends : I -> Sym2 W) (K D : Finset I) (u : W)
    (hDK : D ⊆ K)
    (hmeet : ∀ i ∈ D, ∀ x ∈ ends i,
      ∃ e ∈ D ∩ edgeComponent ends K u,
        ∃ y ∈ ends e, connK ends D x y) :
    D ⊆ edgeComponent ends K u := by
  apply subset_edgeComponent_of_subset_of_rootSpanning_union
    ends K D u hDK
  exact rootSpanning_union_of_edgeComponents_meet ends
    (edgeComponent ends K u) D u
      (edgeComponent_rootSpanning ends K u) hmeet


end StatMech.GrahamGHS.FourColor
