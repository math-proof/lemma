/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareCoverIntersection.Part7
import Structure.StatisticalMechanics.Code.FrontierD.FKRectTorusDisjointWinding
open SimpleGraph


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

theorem FKRectIntegralSquareDartPath.exists_squareCoverDartWitness
    (R : FKRectTorus) {p u : Int × Int}
    {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p
      (p.1 + u.1, p.2 + u.2) l) :
    ∃ C : FKRectSquareCoverDartWitness R u,
      C.darts =
        (fkRectRepeatTranslatedDartPath l u
          (fkRectSquareCoverSide R)).map
            (fkRectIntegralSquareDartMod (fkRectSquareCoverSide R)) := by
  let L := fkRectSquareCoverSide R
  letI : Fact (2 < L) := ⟨fkRectSquareCoverSide_gt_two R⟩
  let repeated := fkRectRepeatTranslatedDartPath l u L
  have hrepeated : FKRectIntegralSquareDartPath p
      (p.1 + (L : Int) * u.1, p.2 + (L : Int) * u.2) repeated :=
    h.repeatTranslated L
  have hpointMod : fkRectIntegralSquarePointMod L p =
      fkRectIntegralSquarePointMod L
        (p.1 + (L : Int) * u.1, p.2 + (L : Int) * u.2) := by
    apply Prod.ext <;> simp [fkRectIntegralSquarePointMod]
  let darts := repeated.map (fkRectIntegralSquareDartMod L)
  have hbalanced : IntegralSquareTorusCycle.DartListBalanced darts :=
    hrepeated.dartListBalanced_of_pointMod_eq L hpointMod
  have hxEquation := hrepeated.displacement_x_eq_wrap (L := L)
  have hyEquation := hrepeated.displacement_y_eq_wrap (L := L)
  rw [hpointMod] at hxEquation hyEquation
  simp only [sub_self, zero_add] at hxEquation hyEquation
  rw [add_sub_cancel_left] at hxEquation hyEquation
  have hL : (L : Int) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans (by norm_num : 0 < 2)
      (fkRectSquareCoverSide_gt_two R)))
  have hxWrap : (darts.map ons_xWrapSign).sum = u.1 := by
    apply mul_left_cancel₀ hL
    exact hxEquation.symm
  have hyWrap : (darts.map ons_yWrapSign).sum = u.2 := by
    apply mul_left_cancel₀ hL
    exact hyEquation.symm
  refine ⟨⟨darts, hbalanced, hxWrap, hyWrap⟩, ?_⟩
  rfl

theorem FKRectSquareCoverDartWitness.not_independent_of_disjointSupport
    {R : FKRectTorus} {u v : Int × Int}
    (C : FKRectSquareCoverDartWitness R u)
    (D : FKRectSquareCoverDartWitness R v)
    (hdisj : ∀ p, FKRectDartListUsesPoint C.darts p →
      ¬ FKRectDartListUsesPoint D.darts p) :
    ¬ FKRectWindingIndependent u v := by
  intro hind
  apply hind
  have hlocal := IntegralSquareTorusCycle.ofDartList_locallyDisjoint
    C.darts D.darts C.balanced D.balanced hdisj
  have hdet :=
    IntegralSquareTorusCycle.dartList_winding_det_eq_zero_of_locallyDisjoint
      C.darts C.balanced D.darts D.balanced hlocal
  rw [C.xWrap_eq, C.yWrap_eq, D.xWrap_eq, D.yWrap_eq] at hdet
  exact hdet


theorem FKRectSquareWalkLift.not_windingIndependent_of_support_disjoint
    (R : FKRectTorus)
    {G H : SimpleGraph R.Vertex} {x y : R.Vertex}
    {w : G.Walk x x} {z : H.Walk y y}
    {p q a b : Int × Int}
    (hw : FKRectSquareWalkLift R w p q)
    (hz : FKRectSquareWalkLift R z a b)
    (hdisj : ∀ v, v ∈ w.support → v ∈ z.support → False) :
    ¬ FKRectWindingIndependent
      (fkRectWalkWinding R w) (fkRectWalkWinding R z) := by
  obtain ⟨l, hl, hlsupp⟩ := hw.exists_supportedIntegralDartPath R
  obtain ⟨k, hk, hksupp⟩ := hz.exists_supportedIntegralDartPath R
  let u := fkRectSquareDeckTranslation R (fkRectWalkWinding R w)
  let v := fkRectSquareDeckTranslation R (fkRectWalkWinding R z)
  have hwu := hw.closed_develop_sub_eq_deck_winding R
  have hzv := hz.closed_develop_sub_eq_deck_winding R
  have hq : fkRectSquareDevelopPoint q =
      ((fkRectSquareDevelopPoint p).1 + u.1,
        (fkRectSquareDevelopPoint p).2 + u.2) := by
    dsimp [u]
    apply Prod.ext
    · have h := congrArg Prod.fst hwu
      simp only [Prod.fst_sub] at h ⊢
      omega
    · have h := congrArg Prod.snd hwu
      simp only [Prod.snd_sub] at h ⊢
      omega
  have hb : fkRectSquareDevelopPoint b =
      ((fkRectSquareDevelopPoint a).1 + v.1,
        (fkRectSquareDevelopPoint a).2 + v.2) := by
    dsimp [v]
    apply Prod.ext
    · have h := congrArg Prod.fst hzv
      simp only [Prod.fst_sub] at h ⊢
      omega
    · have h := congrArg Prod.snd hzv
      simp only [Prod.snd_sub] at h ⊢
      omega
  rw [hq] at hl
  rw [hb] at hk
  obtain ⟨C, hC⟩ := hl.exists_squareCoverDartWitness R
  obtain ⟨D, hD⟩ := hk.exists_squareCoverDartWitness R
  have hls : FKRectIntegralDartListSupportedOn R l
      (fun t => t ∈ w.support) := hlsupp
  have hks : FKRectIntegralDartListSupportedOn R k
      (fun t => t ∈ z.support) := hksupp
  have hlrepeat := hls.repeatTranslated_deck R
    (fkRectWalkWinding R w) (fkRectSquareCoverSide R)
  have hkrepeat := hks.repeatTranslated_deck R
    (fkRectWalkWinding R z) (fkRectSquareCoverSide R)
  have hcoverDisjoint : ∀ t, FKRectDartListUsesPoint C.darts t →
      ¬ FKRectDartListUsesPoint D.darts t := by
    rw [hC, hD]
    exact fkRectDartListUsesPoint_disjoint_of_supported
      R hlrepeat hkrepeat (fun t ht hs => hdisj t ht hs)
  intro hind
  apply C.not_independent_of_disjointSupport D hcoverDisjoint
  exact (fkRectWindingIndependent_squareDeck_iff R _ _).mpr hind


theorem fkRectClosedWalks_not_windingIndependent_of_support_disjoint
    (R : FKRectTorus)
    {G H : SimpleGraph R.Vertex} (hG : G ≤ fkRectTorusGraph R)
    (hH : H ≤ fkRectTorusGraph R)
    {x y : R.Vertex} (w : G.Walk x x) (z : H.Walk y y)
    (hdisj : ∀ v, v ∈ w.support → v ∈ z.support → False) :
    ¬ FKRectWindingIndependent
      (fkRectWalkWinding R w) (fkRectWalkWinding R z) := by
  let p : Int × Int := ((x.1.val : Int), (x.2.val : Int))
  let a : Int × Int := ((y.1.val : Int), (y.2.val : Int))
  have hp : fkRectLiftedVertex R p = x := by
    apply Prod.ext <;> simp [p, fkRectLiftedVertex]
  have ha : fkRectLiftedVertex R a = y := by
    apply Prod.ext <;> simp [a, fkRectLiftedVertex]
  obtain ⟨q, hw⟩ := fkRectWalk_exists_squareLift R hG w p hp
  obtain ⟨b, hz⟩ := fkRectWalk_exists_squareLift R hH z a ha
  exact hw.not_windingIndependent_of_support_disjoint R hz hdisj


theorem fkRectClosedWalks_not_windingIndependent_of_not_reachable
    (R : FKRectTorus) (omega : R.Configuration)
    {x y : R.Vertex}
    (hxy : ¬ (fkRectOpenGraph R omega).Reachable x y)
    (w : (fkRectOpenGraph R omega).Walk x x)
    (z : (fkRectOpenGraph R omega).Walk y y) :
    ¬ FKRectWindingIndependent
      (fkRectWalkWinding R w) (fkRectWalkWinding R z) := by
  apply fkRectClosedWalks_not_windingIndependent_of_support_disjoint R
    (fkRectOpenGraph_le_torusGraph R omega)
    (fkRectOpenGraph_le_torusGraph R omega) w z
  intro v hvw hvz
  have hxv : (fkRectOpenGraph R omega).Reachable x v :=
    (w.takeUntil v hvw).reachable
  have hyv : (fkRectOpenGraph R omega).Reachable y v :=
    (z.takeUntil v hvz).reachable
  exact hxy (hxv.trans hyv.symm)


theorem fkRectClosedWindingSubgroup_cross_dependent
    (R : FKRectTorus) (omega : R.Configuration)
    {x y : R.Vertex}
    (hxy : ¬ (fkRectOpenGraph R omega).Reachable x y) :
    ∀ u ∈ fkRectClosedWindingSubgroup R omega x,
      ∀ v ∈ fkRectClosedWindingSubgroup R omega y,
        ¬ FKRectWindingIndependent u v := by
  rintro u ⟨w, rfl⟩ v ⟨z, rfl⟩
  exact fkRectClosedWalks_not_windingIndependent_of_not_reachable
    R omega hxy w z


theorem not_windingIndependent_add_of_pairwise
    (a b c d : Int × Int)
    (hab : ¬ FKRectWindingIndependent a b)
    (had : ¬ FKRectWindingIndependent a d)
    (hbc : ¬ FKRectWindingIndependent b c)
    (hcd : ¬ FKRectWindingIndependent c d) :
    ¬ FKRectWindingIndependent (a + c) (b + d) := by
  unfold FKRectWindingIndependent at hab had hbc hcd ⊢
  simp only [not_ne_iff, Prod.fst_add, Prod.snd_add] at *
  linear_combination hab + had - hbc + hcd


theorem windingSubgroup_sup_not_rankTwo_of_pairwise_dependent
    (H K : AddSubgroup (Int × Int))
    (hH : ∀ a ∈ H, ∀ b ∈ H, ¬ FKRectWindingIndependent a b)
    (hK : ∀ a ∈ K, ∀ b ∈ K, ¬ FKRectWindingIndependent a b)
    (hHK : ∀ a ∈ H, ∀ b ∈ K, ¬ FKRectWindingIndependent a b) :
    ¬ ∃ a ∈ H ⊔ K, ∃ b ∈ H ⊔ K,
      FKRectWindingIndependent a b := by
  rintro ⟨a, ha, b, hb, hind⟩
  rw [AddSubgroup.mem_sup] at ha hb
  obtain ⟨x, hx, y, hy, rfl⟩ := ha
  obtain ⟨z, hz, t, ht, rfl⟩ := hb
  exact (not_windingIndependent_add_of_pairwise x z y t
    (hH x hx z hz) (hHK x hx t ht)
    (hHK z hz y hy) (hK y hy t ht)) hind

end
end StatMech.FrontierD
