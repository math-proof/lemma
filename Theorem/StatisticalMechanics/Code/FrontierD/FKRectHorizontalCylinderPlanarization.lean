/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderPlanarization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderExploration
import Theorem.StatisticalMechanics.Code.FrontierD.FKFreeConnectionBoxEmbedding
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingEvent.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulHorizontalExtension
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulCarrierDisjoint
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulShearCoordinates
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulWalkVerticalBound
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDisjointWinding.Part4
open Finset SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem not_fkRectCrossesVerticalSeam_indexedEdge_of_not_horizontalCut
    (R : FKRectTorus) (a : R.EdgeIndex)
    (ha : a ∉ fkRectHorizontalCutEdges R) :
    ¬ fkRectCrossesVerticalSeam R (fkRectTorusIndexedEdge R a) := by
  rw [mem_fkRectHorizontalCutEdges_iff] at ha
  rcases a with ⟨b, x, y⟩
  change y.val ≠ 0 at ha
  have hh := R.height_gt_two
  have hylt := y.isLt
  intro hcross
  cases b
  · by_cases hy : Even y.val <;>
      simp only [fkRectTorusIndexedEdge, Bool.false_eq_true, if_false,
        hy, if_true, fkRectCrossesVerticalSeam_mk] at hcross
    all_goals rw [fkRectCyclicPred_val] at hcross
    all_goals split at hcross <;> omega
  · simp only [fkRectTorusIndexedEdge, if_true,
      fkRectCrossesVerticalSeam_mk] at hcross
    rw [fkRectCyclicPred_val] at hcross
    split at hcross <;> omega

theorem fkRectCrossesVerticalSeam_indexedEdge_of_horizontalCut_planarization
    (R : FKRectTorus) (a : R.EdgeIndex)
    (ha : a ∈ fkRectHorizontalCutEdges R) :
    fkRectCrossesVerticalSeam R (fkRectTorusIndexedEdge R a) := by
  rw [mem_fkRectHorizontalCutEdges_iff] at ha
  rcases a with ⟨b, x, y⟩
  change y.val = 0 at ha
  have hlast : R.height - 1 + 1 = R.height := by omega
  cases b
  · by_cases hy : Even y.val <;>
      simp only [fkRectTorusIndexedEdge, Bool.false_eq_true, if_false,
        hy, if_true, fkRectCrossesVerticalSeam_mk]
    all_goals rw [fkRectCyclicPred_val]
    all_goals simp only [ha, if_true]
    all_goals exact Or.inl ⟨True.intro, hlast⟩
  · simp only [fkRectTorusIndexedEdge, if_true,
      fkRectCrossesVerticalSeam_mk]
    rw [fkRectCyclicPred_val]
    simp only [ha, if_true]
    exact Or.inl ⟨True.intro, hlast⟩


theorem fkRectHorizontalCylinderGraph_not_crossesVerticalSeam
    (R : FKRectTorus) {x y : R.Vertex}
    (hxy : (fkRectHorizontalCylinderGraph R).Adj x y) :
    ¬ fkRectCrossesVerticalSeam R s(x, y) := by
  obtain ⟨htorus, hcut⟩ :=
    (fkRectHorizontalCylinderGraph_adj_iff R x y).mp hxy
  obtain ⟨a, ha⟩ := htorus
  have hacut : a ∉ fkRectHorizontalCutEdges R := by
    intro hacut
    apply hcut
    rw [← ha]
    exact (mem_fkRectHorizontalCutGraphEdges R a).2 hacut
  rw [← ha]
  exact not_fkRectCrossesVerticalSeam_indexedEdge_of_not_horizontalCut
    R a hacut


theorem fkRectHorizontalCylinderWalk_winding_snd_eq_zero
    (R : FKRectTorus) {x y : R.Vertex}
    (p : (fkRectHorizontalCylinderGraph R).Walk x y) :
    (fkRectWalkWinding R p).2 = 0 := by
  induction p with
  | nil => rfl
  | @cons u v w huv p ih =>
      simp only [fkRectWalkWinding]
      rw [fkRectVerticalSeamIncrement_eq_zero_of_not_crosses R u v
        (fkRectHorizontalCylinderGraph_not_crossesVerticalSeam R huv),
        ih, zero_add]

theorem fkRectFaithfulShearDartRoute_snd_between
    (d : FKRectIntegralSquareDart) (r : Int × Int)
    (hr : r ∈ fkRectFaithfulShearDartRoute d) :
    min ((fkRectFaithfulShearPoint d.1) 1)
          ((fkRectFaithfulShearPoint
            (fkRectIntegralSquareDartEnd d)) 1) ≤
        (fkRectPairSite r) 1 ∧
      (fkRectPairSite r) 1 ≤
        max ((fkRectFaithfulShearPoint d.1) 1)
          ((fkRectFaithfulShearPoint
            (fkRectIntegralSquareDartEnd d)) 1) := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  rcases r with ⟨a, b⟩
  fin_cases mu <;>
    simp [fkRectFaithfulShearDartRoute, fkRectFaithfulShearPoint,
      fkRectFaithfulShearPair, fkRectPairSite,
      fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY] at hr ⊢ <;>
    omega

theorem fkRectFaithfulShearDartRoute_bounds
    {lower upper : Int} (d : FKRectIntegralSquareDart)
    (hstart : lower ≤ (fkRectFaithfulShearPoint d.1) 1 ∧
      (fkRectFaithfulShearPoint d.1) 1 ≤ upper)
    (hend : lower ≤
        (fkRectFaithfulShearPoint
          (fkRectIntegralSquareDartEnd d)) 1 ∧
      (fkRectFaithfulShearPoint
        (fkRectIntegralSquareDartEnd d)) 1 ≤ upper)
    {z : StatMech.Lattice.Site 2} {r : Int × Int}
    (hr : r ∈ fkRectFaithfulShearDartRoute d)
    (hz : z = fkRectPairSite r) :
    lower ≤ z 1 ∧ z 1 ≤ upper := by
  subst z
  have hbetween := fkRectFaithfulShearDartRoute_snd_between d r hr
  constructor
  · exact le_trans (le_min hstart.1 hend.1) hbetween.1
  · exact le_trans hbetween.2 (max_le hstart.2 hend.2)

theorem FKRectIntegralSquareDartPath.exists_faithfulShearWalk_bounds
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p q l) (hl : l ≠ [])
    {lower upper : Int}
    (hbounds : ∀ d ∈ l,
      (lower ≤ (fkRectFaithfulShearPoint d.1) 1 ∧
        (fkRectFaithfulShearPoint d.1) 1 ≤ upper) ∧
      (lower ≤
          (fkRectFaithfulShearPoint
            (fkRectIntegralSquareDartEnd d)) 1 ∧
        (fkRectFaithfulShearPoint
          (fkRectIntegralSquareDartEnd d)) 1 ≤ upper)) :
    ∃ V : (StatMech.Lattice.hypercubicLattice 2).Walk
        (fkRectFaithfulShearPoint p) (fkRectFaithfulShearPoint q),
      ∀ z ∈ V.support, lower ≤ z 1 ∧ z 1 ≤ upper := by
  obtain ⟨V, hV⟩ := h.exists_faithfulShearWalk_of_ne_nil hl
  refine ⟨V, ?_⟩
  intro z hz
  obtain ⟨d, hdl, r, hr, hz⟩ := hV z hz
  exact fkRectFaithfulShearDartRoute_bounds d
    (hbounds d hdl).1 (hbounds d hdl).2 hr hz

theorem FKRectSquareWalkLift.end_snd_eq_val_of_cylinder
    (R : FKRectTorus) {x y : R.Vertex}
    {w : (fkRectHorizontalCylinderGraph R).Walk x y}
    {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q)
    (hpRow : p.2 = (x.2.val : Int)) :
    q.2 = (y.2.val : Int) := by
  induction h with
  | nil => exact hpRow
  | @cons a b c hab tail p q r hpa hqb hdisp haxis hlift ih =>
      have hno := fkRectHorizontalCylinderGraph_not_crossesVerticalSeam R hab
      have hinc : fkRectVerticalSeamIncrement R a b = 0 :=
        fkRectVerticalSeamIncrement_eq_zero_of_not_crosses R a b hno
      have hqRow : q.2 = (b.2.val : Int) := by
        have hsnd := congrArg Prod.snd hdisp
        simp only [Prod.snd_sub, fkRectDevelopedStep] at hsnd
        rw [hinc] at hsnd
        simp only [mul_zero, add_zero] at hsnd
        omega
      exact ih hqRow

theorem FKRectSquareWalkLift.exists_cylinderSupportedIntegralDartPath
    (R : FKRectTorus) {x y : R.Vertex}
    {w : (fkRectHorizontalCylinderGraph R).Walk x y}
    {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q)
    (hpRow : p.2 = (x.2.val : Int)) :
    ∃ l : List FKRectIntegralSquareDart,
      FKRectIntegralSquareDartPath
        (fkRectSquareDevelopPoint p) (fkRectSquareDevelopPoint q) l ∧
      FKRectIntegralDartListSupportedOn R l (fun v => v ∈ w.support) ∧
      (∀ d ∈ l,
        (0 ≤ (fkRectFaithfulShearPoint d.1) 1 ∧
          (fkRectFaithfulShearPoint d.1) 1 ≤ 2 * (R.height - 1)) ∧
        (0 ≤
            (fkRectFaithfulShearPoint
              (fkRectIntegralSquareDartEnd d)) 1 ∧
          (fkRectFaithfulShearPoint
            (fkRectIntegralSquareDartEnd d)) 1 ≤
              2 * (R.height - 1))) := by
  induction h with
  | nil p hp =>
      exact ⟨[], FKRectIntegralSquareDartPath.nil _,
        by simp [FKRectIntegralDartListSupportedOn],
        by simp⟩
  | @cons a b c hab tail p q r hpa hqb hdisp haxis hlift ih =>
      have hno := fkRectHorizontalCylinderGraph_not_crossesVerticalSeam R hab
      have hinc : fkRectVerticalSeamIncrement R a b = 0 :=
        fkRectVerticalSeamIncrement_eq_zero_of_not_crosses R a b hno
      have hqRow : q.2 = (b.2.val : Int) := by
        have hsnd := congrArg Prod.snd hdisp
        simp only [Prod.snd_sub, fkRectDevelopedStep] at hsnd
        rw [hinc] at hsnd
        simp only [mul_zero, add_zero] at hsnd
        omega
      obtain ⟨l, hlpath, hlsupp, hlbounds⟩ := ih hqRow
      obtain ⟨mu, hmu⟩ := haxis.exists_direction
      let d : FKRectIntegralSquareDart :=
        (fkRectSquareDevelopPoint p, mu)
      have hdend : fkRectIntegralSquareDartEnd d =
          fkRectSquareDevelopPoint q := by
        exact hmu
      refine ⟨d :: l,
        FKRectIntegralSquareDartPath.cons d hdend hlpath, ?_, ?_⟩
      · intro e he
        rcases List.mem_cons.mp he with rfl | he
        · constructor
          · rw [fkRectSquareRepresentativeVertex_developPoint, hpa]
            simp
          · rw [hdend, fkRectSquareRepresentativeVertex_developPoint, hqb]
            simp
        · obtain ⟨hstart, hend⟩ := hlsupp e he
          constructor <;>
            rw [SimpleGraph.Walk.support_cons] <;>
            exact List.mem_cons_of_mem a (by assumption)
      · intro e he
        rcases List.mem_cons.mp he with rfl | he
        · have haLt := a.2.isLt
          have hbLt := b.2.isLt
          have hstartY :
              (fkRectFaithfulShearPoint
                (fkRectSquareDevelopPoint p)) 1 = 2 * p.2 := by
            rw [fkRectFaithfulShearPoint_apply_one]
            linear_combination 2 *
              (fkRectSquareDevelopPoint_fst_sub_snd p)
          have hendY :
              (fkRectFaithfulShearPoint
                (fkRectIntegralSquareDartEnd d)) 1 = 2 * q.2 := by
            rw [hdend, fkRectFaithfulShearPoint_apply_one]
            linear_combination 2 *
              (fkRectSquareDevelopPoint_fst_sub_snd q)
          rw [hstartY, hendY, hpRow, hqRow]
          constructor <;> constructor <;> omega
        · exact hlbounds e he

theorem fkRectFaithfulShearPoint_translate_snd_of_eq
    (d u : Int × Int) (hu : u.1 = u.2) :
    (fkRectFaithfulShearPoint (d.1 + u.1, d.2 + u.2)) 1 =
      (fkRectFaithfulShearPoint d) 1 := by
  simp only [fkRectFaithfulShearPoint_apply_one]
  omega

theorem fkRectFaithfulDartBounds_translate_of_eq
    {lower upper : Int} (u : Int × Int) (hu : u.1 = u.2)
    (d : FKRectIntegralSquareDart)
    (h : (lower ≤ (fkRectFaithfulShearPoint d.1) 1 ∧
        (fkRectFaithfulShearPoint d.1) 1 ≤ upper) ∧
      (lower ≤
          (fkRectFaithfulShearPoint
            (fkRectIntegralSquareDartEnd d)) 1 ∧
        (fkRectFaithfulShearPoint
          (fkRectIntegralSquareDartEnd d)) 1 ≤ upper)) :
    (lower ≤
        (fkRectFaithfulShearPoint
          (fkRectIntegralSquareDartTranslate u d).1) 1 ∧
      (fkRectFaithfulShearPoint
        (fkRectIntegralSquareDartTranslate u d).1) 1 ≤ upper) ∧
    (lower ≤
        (fkRectFaithfulShearPoint
          (fkRectIntegralSquareDartEnd
            (fkRectIntegralSquareDartTranslate u d))) 1 ∧
      (fkRectFaithfulShearPoint
        (fkRectIntegralSquareDartEnd
          (fkRectIntegralSquareDartTranslate u d))) 1 ≤ upper) := by
  have hstart := fkRectFaithfulShearPoint_translate_snd_of_eq d.1 u hu
  have hend := fkRectFaithfulShearPoint_translate_snd_of_eq
    (fkRectIntegralSquareDartEnd d) u hu
  rw [fkRectIntegralSquareDartEnd_translate]
  simpa [fkRectIntegralSquareDartTranslate, hstart, hend] using h

theorem fkRectRepeatTranslatedDartPath_faithfulBounds
    {lower upper : Int} (l : List FKRectIntegralSquareDart)
    (u : Int × Int) (hu : u.1 = u.2)
    (hl : ∀ d ∈ l,
      (lower ≤ (fkRectFaithfulShearPoint d.1) 1 ∧
        (fkRectFaithfulShearPoint d.1) 1 ≤ upper) ∧
      (lower ≤
          (fkRectFaithfulShearPoint
            (fkRectIntegralSquareDartEnd d)) 1 ∧
        (fkRectFaithfulShearPoint
          (fkRectIntegralSquareDartEnd d)) 1 ≤ upper)) :
    ∀ n d, d ∈ fkRectRepeatTranslatedDartPath l u n →
      (lower ≤ (fkRectFaithfulShearPoint d.1) 1 ∧
        (fkRectFaithfulShearPoint d.1) 1 ≤ upper) ∧
      (lower ≤
          (fkRectFaithfulShearPoint
            (fkRectIntegralSquareDartEnd d)) 1 ∧
        (fkRectFaithfulShearPoint
          (fkRectIntegralSquareDartEnd d)) 1 ≤ upper) := by
  intro n
  induction n with
  | zero => simp [fkRectRepeatTranslatedDartPath]
  | succ n ih =>
      intro d hd
      rw [fkRectRepeatTranslatedDartPath, List.mem_append] at hd
      rcases hd with hd | hd
      · exact ih d hd
      · obtain ⟨e, hel, rfl⟩ := List.mem_map.mp hd
        apply fkRectFaithfulDartBounds_translate_of_eq
          (fkRectNatScale n u)
        · simp [fkRectNatScale, hu]
        · exact hl e hel

theorem FKRectIntegralDartListSupportedOn.translate_deck
    (R : FKRectTorus) {l : List FKRectIntegralSquareDart}
    {S : R.Vertex → Prop}
    (h : FKRectIntegralDartListSupportedOn R l S) (u : Int × Int) :
    FKRectIntegralDartListSupportedOn R
      (l.map (fkRectIntegralSquareDartTranslate
        (fkRectSquareDeckTranslation R u))) S := by
  intro d hd
  obtain ⟨e, hel, rfl⟩ := List.mem_map.mp hd
  constructor
  · rw [fkRectSquareRepresentativeVertex_dartTranslate_deck]
    exact (h e hel).1
  · rw [fkRectSquareRepresentativeVertex_dartTranslateEnd_deck]
    exact (h e hel).2

theorem FKRectIntegralDartListSupportedOn.common_of_incident
    (R : FKRectTorus) {l k : List FKRectIntegralSquareDart}
    {S T : R.Vertex → Prop}
    (hl : FKRectIntegralDartListSupportedOn R l S)
    (hk : FKRectIntegralDartListSupportedOn R k T)
    {d e : FKRectIntegralSquareDart} (hdl : d ∈ l) (hek : e ∈ k)
    (hde : FKRectIntegralSquareDartsIncident d e) :
    ∃ v, S v ∧ T v := by
  rcases hde with h | h | h | h
  · exact ⟨fkRectSquareRepresentativeVertex R d.1,
      (hl d hdl).1, h ▸ (hk e hek).1⟩
  · exact ⟨fkRectSquareRepresentativeVertex R d.1,
      (hl d hdl).1, h ▸ (hk e hek).2⟩
  · exact ⟨fkRectSquareRepresentativeVertex R
        (fkRectIntegralSquareDartEnd d),
      (hl d hdl).2, h ▸ (hk e hek).1⟩
  · exact ⟨fkRectSquareRepresentativeVertex R
        (fkRectIntegralSquareDartEnd d),
      (hl d hdl).2, h ▸ (hk e hek).2⟩

theorem exists_fkRectFaithfulWalk_horizontal_natAbs_bound
    {x y : StatMech.Lattice.Site 2}
    (W : (StatMech.Lattice.hypercubicLattice 2).Walk x y) :
    ∃ M : Nat, ∀ z ∈ W.support,
      -(M : Int) ≤ z 0 ∧ z 0 ≤ (M : Int) := by
  let swap : StatMech.Lattice.Site 2 → StatMech.Lattice.Site 2 :=
    fun z => ![z 1, z 0]
  have hswap : ∀ {a b},
      (StatMech.Lattice.hypercubicLattice 2).Adj a b →
        (StatMech.Lattice.hypercubicLattice 2).Adj (swap a) (swap b) := by
    intro a b hab
    rw [StatMech.Lattice.hypercubicLattice_adj,
      Fin.sum_univ_two] at hab ⊢
    simp [swap]
    omega
  let f : StatMech.Lattice.hypercubicLattice 2 →g
      StatMech.Lattice.hypercubicLattice 2 := ⟨swap, hswap⟩
  obtain ⟨M, hM⟩ :=
    exists_fkRectFaithfulWalk_vertical_natAbs_bound (W.map f)
  refine ⟨M, ?_⟩
  intro z hz
  have hzmap : swap z ∈ (W.map f).support := by
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨z, hz, rfl⟩
  simpa [swap] using hM (swap z) hzmap

theorem fkRectHorizontalCylinder_support_intersects_bottomTop_of_pos
    (R : FKRectTorus) (bottomX topX : Fin R.width)
    (V : (fkRectHorizontalCylinderGraph R).Walk
      (bottomX, fkRectBottomRow R) (topX, fkRectTopRow R))
    {x : R.Vertex}
    (W : (fkRectHorizontalCylinderGraph R).Walk x x)
    (hwind : 0 < (fkRectWalkWinding R W).1) :
    ∃ v, v ∈ W.support ∧ v ∈ V.support := by
  let hsub : fkRectHorizontalCylinderGraph R ≤ fkRectTorusGraph R := by
    intro a b hab
    exact (fkRectHorizontalCylinderGraph_adj_iff R a b).mp hab |>.1
  let pv : Int × Int := ((bottomX.val : Int), 0)
  let pw : Int × Int := ((x.1.val : Int), (x.2.val : Int))
  have hpv : fkRectLiftedVertex R pv =
      (bottomX, fkRectBottomRow R) := by
    apply Prod.ext
    · simp [pv, fkRectLiftedVertex]
    · change fkRectIntModFin R.height_pos 0 = fkRectBottomRow R
      rw [show (0 : Int) = ((fkRectBottomRow R).val : Int) by
        simp [fkRectBottomRow]]
      exact fkRectIntModFin_natCast R.height_pos _
  have hpw : fkRectLiftedVertex R pw = x := by
    apply Prod.ext <;> simp [pw, fkRectLiftedVertex]
  obtain ⟨qv, hVlift⟩ :=
    fkRectWalk_exists_squareLift R hsub V pv hpv
  obtain ⟨qw, hWlift⟩ :=
    fkRectWalk_exists_squareLift R hsub W pw hpw
  have hpvRow : pv.2 =
      (((bottomX, fkRectBottomRow R) : R.Vertex).2.val : Int) := by
    simp [pv, fkRectBottomRow]
  have hpwRow : pw.2 = (x.2.val : Int) := by rfl
  have hqvRow : qv.2 =
      (((topX, fkRectTopRow R) : R.Vertex).2.val : Int) :=
    hVlift.end_snd_eq_val_of_cylinder R hpvRow
  have hqwRow : qw.2 = (x.2.val : Int) :=
    hWlift.end_snd_eq_val_of_cylinder R hpwRow
  obtain ⟨lv, hLvPath, hLvSupp, hLvBounds⟩ :=
    hVlift.exists_cylinderSupportedIntegralDartPath R hpvRow
  obtain ⟨lw, hLwPath, hLwSupp, hLwBounds⟩ :=
    hWlift.exists_cylinderSupportedIntegralDartPath R hpwRow
  have hpvqv : fkRectSquareDevelopPoint pv ≠
      fkRectSquareDevelopPoint qv := by
    intro heq
    have hpq : pv = qv := fkRectSquareDevelopPoint_injective heq
    have hh := R.height_gt_two
    have hsnd := congrArg Prod.snd hpq
    rw [hpvRow, hqvRow] at hsnd
    simp [fkRectBottomRow, fkRectTopRow] at hsnd
    omega
  have hlv : lv ≠ [] := hLvPath.ne_nil_of_ne hpvqv
  obtain ⟨Vfaithful, hVfaithful⟩ :=
    hLvPath.exists_faithfulShearWalk_of_ne_nil hlv
  let H : Int := 2 * (R.height - 1)
  have hVvertical : ∀ z ∈ Vfaithful.support,
      0 ≤ z 1 ∧ z 1 ≤ H := by
    intro z hz
    obtain ⟨d, hdl, r, hr, hz⟩ := hVfaithful z hz
    exact fkRectFaithfulShearDartRoute_bounds d
      (hLvBounds d hdl).1 (hLvBounds d hdl).2 hr hz
  obtain ⟨B, hVB⟩ :=
    exists_fkRectFaithfulWalk_horizontal_natAbs_bound Vfaithful
  let wind := fkRectWalkWinding R W
  have hwindSnd : wind.2 = 0 := by
    exact fkRectHorizontalCylinderWalk_winding_snd_eq_zero R W
  let u := fkRectSquareDeckTranslation R wind
  have huEq : u.1 = u.2 := by
    simp [u, wind, fkRectSquareDeckTranslation, hwindSnd]
  have hqwDevelop : fkRectSquareDevelopPoint qw =
      ((fkRectSquareDevelopPoint pw).1 + u.1,
        (fkRectSquareDevelopPoint pw).2 + u.2) := by
    have h := hWlift.closed_develop_sub_eq_deck_winding R
    apply Prod.ext
    · have hx := congrArg Prod.fst h
      simp only [Prod.fst_sub] at hx ⊢
      dsimp [u, wind]
      omega
    · have hy := congrArg Prod.snd h
      simp only [Prod.snd_sub] at hy ⊢
      dsimp [u, wind]
      omega
  have hpwqw : fkRectSquareDevelopPoint pw ≠
      fkRectSquareDevelopPoint qw := by
    intro heq
    have hx := congrArg (fun z : Int × Int => z.1) heq
    rw [hqwDevelop] at hx
    have huPos : 0 < u.1 := by
      have hwpos : (0 : Int) < R.width := by
        exact_mod_cast R.width_pos
      simpa [u, wind, fkRectSquareDeckTranslation, hwindSnd] using
        mul_pos hwpos hwind
    change (fkRectSquareDevelopPoint pw).1 =
      (fkRectSquareDevelopPoint pw).1 + u.1 at hx
    omega
  have hlw : lw ≠ [] := hLwPath.ne_nil_of_ne hpwqw
  let X : Int := (fkRectFaithfulShearPoint
    (fkRectSquareDevelopPoint pw)) 0
  let m : Nat := B + X.natAbs + 1
  let shiftWind : Int × Int :=
    (-((m : Int) * wind.1), 0)
  let shift := fkRectSquareDeckTranslation R shiftWind
  let ps : Int × Int :=
    ((fkRectSquareDevelopPoint pw).1 + shift.1,
      (fkRectSquareDevelopPoint pw).2 + shift.2)
  let lshift := lw.map (fkRectIntegralSquareDartTranslate shift)
  have hShiftPath : FKRectIntegralSquareDartPath ps
      (ps.1 + u.1, ps.2 + u.2) lshift := by
    rw [hqwDevelop] at hLwPath
    have ht := hLwPath.translate shift
    have hend :
        (((fkRectSquareDevelopPoint pw).1 + u.1 + shift.1,
            (fkRectSquareDevelopPoint pw).2 + u.2 + shift.2)) =
          (ps.1 + u.1, ps.2 + u.2) := by
      apply Prod.ext <;> simp [ps] <;> ring
    rw [hend] at ht
    exact ht
  have hShiftSupp : FKRectIntegralDartListSupportedOn R lshift
      (fun v => v ∈ W.support) := by
    simpa [lshift, shift] using hLwSupp.translate_deck R shiftWind
  have hShiftBounds : ∀ d ∈ lshift,
      (0 ≤ (fkRectFaithfulShearPoint d.1) 1 ∧
        (fkRectFaithfulShearPoint d.1) 1 ≤ H) ∧
      (0 ≤
          (fkRectFaithfulShearPoint
            (fkRectIntegralSquareDartEnd d)) 1 ∧
        (fkRectFaithfulShearPoint
          (fkRectIntegralSquareDartEnd d)) 1 ≤ H) := by
    intro d hd
    obtain ⟨e, hel, rfl⟩ := List.mem_map.mp hd
    apply fkRectFaithfulDartBounds_translate_of_eq shift
    · simp [shift, shiftWind, fkRectSquareDeckTranslation]
    · exact hLwBounds e hel
  let n : Nat := 2 * m
  let lrep := fkRectRepeatTranslatedDartPath lshift u n
  have hRepPath : FKRectIntegralSquareDartPath ps
      (ps.1 + (n : Int) * u.1, ps.2 + (n : Int) * u.2) lrep := by
    exact hShiftPath.repeatTranslated n
  have hRepSupp : FKRectIntegralDartListSupportedOn R lrep
      (fun v => v ∈ W.support) := by
    have h := hShiftSupp.repeatTranslated_deck R wind n
    simpa [lrep, u] using h
  have hRepBounds : ∀ d ∈ lrep,
      (0 ≤ (fkRectFaithfulShearPoint d.1) 1 ∧
        (fkRectFaithfulShearPoint d.1) 1 ≤ H) ∧
      (0 ≤
          (fkRectFaithfulShearPoint
            (fkRectIntegralSquareDartEnd d)) 1 ∧
        (fkRectFaithfulShearPoint
          (fkRectIntegralSquareDartEnd d)) 1 ≤ H) := by
    exact fkRectRepeatTranslatedDartPath_faithfulBounds
      lshift u huEq hShiftBounds n
  have hmp : 0 < m := by simp [m]
  have hnp : 0 < n := by simp [n, hmp]
  have huPos : 0 < u.1 := by
    have hwpos : (0 : Int) < R.width := by
      exact_mod_cast R.width_pos
    simpa [u, wind, fkRectSquareDeckTranslation, hwindSnd] using
      mul_pos hwpos hwind
  have hRepEndpoints : ps ≠
      (ps.1 + (n : Int) * u.1, ps.2 + (n : Int) * u.2) := by
    intro heq
    have hx := congrArg Prod.fst heq
    change ps.1 = ps.1 + (n : Int) * u.1 at hx
    have hnInt : (0 : Int) < n := by exact_mod_cast hnp
    nlinarith
  have hlrep : lrep ≠ [] := hRepPath.ne_nil_of_ne hRepEndpoints
  obtain ⟨Wfaithful, hWfaithful⟩ :=
    hRepPath.exists_faithfulShearWalk_of_ne_nil hlrep
  have hWvertical : ∀ z ∈ Wfaithful.support,
      0 ≤ z 1 ∧ z 1 ≤ H := by
    intro z hz
    obtain ⟨d, hdl, r, hr, hz⟩ := hWfaithful z hz
    exact fkRectFaithfulShearDartRoute_bounds d
      (hRepBounds d hdl).1 (hRepBounds d hdl).2 hr hz
  have hshiftEq : shift =
      (-((m : Int) * u.1), -((m : Int) * u.2)) := by
    apply Prod.ext <;>
      simp [shift, shiftWind, u, wind, fkRectSquareDeckTranslation,
        hwindSnd] <;>
      ring
  have hWstart : (fkRectFaithfulShearPoint ps) 0 ≤ -(B : Int) := by
    have hX : -(X.natAbs : Int) ≤ X := by
      rw [Int.natCast_natAbs]
      exact neg_abs_le X
    have huOne : 1 ≤ 2 * (u.1 + u.2) := by
      rw [huEq]
      omega
    have hmInt : (m : Int) = B + X.natAbs + 1 := by
      simp [m]
    have hcoord : (fkRectFaithfulShearPoint ps) 0 =
        X - (m : Int) * (2 * (u.1 + u.2)) := by
      rw [fkRectFaithfulShearPoint_apply_zero]
      dsimp [ps]
      rw [hshiftEq]
      dsimp [X]
      rw [fkRectFaithfulShearPoint_apply_zero]
      ring
    rw [hcoord]
    have hmul := mul_le_mul_of_nonneg_left huOne
      (show (0 : Int) ≤ m by positivity)
    omega
  have hWend : (B : Int) ≤
      (fkRectFaithfulShearPoint
        (ps.1 + (n : Int) * u.1,
          ps.2 + (n : Int) * u.2)) 0 := by
    have hX : X ≤ (X.natAbs : Int) := by
      rw [Int.natCast_natAbs]
      exact le_abs_self X
    have huOne : 1 ≤ 2 * (u.1 + u.2) := by
      rw [huEq]
      omega
    have hmInt : (m : Int) = B + X.natAbs + 1 := by
      simp [m]
    have hcoord :
        (fkRectFaithfulShearPoint
          (ps.1 + (n : Int) * u.1,
            ps.2 + (n : Int) * u.2)) 0 =
          X + (m : Int) * (2 * (u.1 + u.2)) := by
      rw [fkRectFaithfulShearPoint_apply_zero]
      dsimp [ps, n]
      rw [hshiftEq]
      dsimp [X]
      rw [fkRectFaithfulShearPoint_apply_zero]
      ring
    rw [hcoord]
    have hmul := mul_le_mul_of_nonneg_left huOne
      (show (0 : Int) ≤ m by positivity)
    omega
  obtain ⟨M, hWM⟩ :=
    exists_fkRectFaithfulWalk_horizontal_natAbs_bound Wfaithful
  let K : Nat := max B M + 1
  let alpha : Int := -(K : Int)
  let beta : Int := K
  have hKpos : (0 : Int) < K := by simp [K]
  have hBK : (B : Int) ≤ K := by
    exact_mod_cast (Nat.le_trans (Nat.le_max_left B M) (Nat.le_add_right _ _))
  have hMK : (M : Int) ≤ K := by
    exact_mod_cast (Nat.le_trans (Nat.le_max_right B M) (Nat.le_add_right _ _))
  have hVrect : ∀ z ∈ Vfaithful.support,
      z ∈ rect alpha beta 0 H := by
    intro z hz
    rw [mem_rect]
    have hx := hVB z hz
    have hy := hVvertical z hz
    dsimp [alpha, beta]
    omega
  have hWrect : ∀ z ∈ Wfaithful.support,
      z ∈ rect alpha beta 0 H := by
    intro z hz
    rw [mem_rect]
    have hx := hWM z hz
    have hy := hWvertical z hz
    dsimp [alpha, beta]
    omega
  have hpvY :
      (fkRectFaithfulShearPoint (fkRectSquareDevelopPoint pv)) 1 = 0 := by
    rw [fkRectFaithfulShearPoint_apply_one]
    have h := fkRectSquareDevelopPoint_fst_sub_snd pv
    simp [pv] at h ⊢
    omega
  have hqvY :
      (fkRectFaithfulShearPoint (fkRectSquareDevelopPoint qv)) 1 = H := by
    rw [fkRectFaithfulShearPoint_apply_one]
    have h := fkRectSquareDevelopPoint_fst_sub_snd qv
    simp [fkRectTopRow] at hqvRow
    dsimp [H]
    omega
  let Vcross : (hypercubicLattice 2).Walk
      ![(fkRectFaithfulShearPoint
          (fkRectSquareDevelopPoint pv)) 0, 0]
      ![(fkRectFaithfulShearPoint
          (fkRectSquareDevelopPoint qv)) 0, H] :=
    Vfaithful.copy (by
      funext i
      fin_cases i <;> simp [hpvY]) (by
      funext i
      fin_cases i <;> simp [hqvY])
  have hVcrossRect : ∀ z ∈ Vcross.support,
      z ∈ rect alpha beta 0 H := by
    intro z hz
    apply hVrect z
    simpa [Vcross] using hz
  have hfaithfulIntersection : ∃ z,
      z ∈ Wfaithful.support ∧ z ∈ Vfaithful.support := by
    by_contra hnone
    push Not at hnone
    let Wcross := fkRectFaithfulHorizontalExtension alpha beta Wfaithful
    have hWcrossRect : ∀ z ∈ Wcross.support,
        z ∈ rect alpha beta 0 H := by
      apply fkRectFaithfulHorizontalExtension_support_rect
        alpha beta 0 H Wfaithful
      · have := hWM (fkRectFaithfulShearPoint ps)
          Wfaithful.start_mem_support
        dsimp [alpha]
        omega
      · have := hWM
          (fkRectFaithfulShearPoint
            (ps.1 + (n : Int) * u.1,
              ps.2 + (n : Int) * u.2))
          Wfaithful.end_mem_support
        dsimp [beta]
        omega
      · exact hWrect
    have hWcrossDisjoint : ∀ z, z ∈ Wcross.support →
        z ∈ Vfaithful.support → False := by
      apply fkRectFaithfulHorizontalExtension_support_disjoint_of_core_bounds
        alpha beta (-(B : Int)) (B : Int) Wfaithful Vfaithful
      · have := hWM (fkRectFaithfulShearPoint ps)
          Wfaithful.start_mem_support
        dsimp [alpha]
        omega
      · exact hWstart
      · exact hWend
      · have := hWM
          (fkRectFaithfulShearPoint
            (ps.1 + (n : Int) * u.1,
              ps.2 + (n : Int) * u.2))
          Wfaithful.end_mem_support
        dsimp [beta]
        omega
      · exact hVB
      · exact fun z hzW hzV => hnone z hzW hzV
    have hWstartRect := hWcrossRect
      ![alpha, (fkRectFaithfulShearPoint ps) 1]
      Wcross.start_mem_support
    have hWendRect := hWcrossRect
      ![beta,
        (fkRectFaithfulShearPoint
          (ps.1 + (n : Int) * u.1,
            ps.2 + (n : Int) * u.2)) 1]
      Wcross.end_mem_support
    obtain ⟨z, hzW, hzV⟩ :=
      fkRectFaithful_bottomTop_leftRight_support_intersects
        alpha beta 0 H
        ((fkRectFaithfulShearPoint
          (fkRectSquareDevelopPoint pv)) 0)
        ((fkRectFaithfulShearPoint
          (fkRectSquareDevelopPoint qv)) 0)
        (by dsimp [alpha, beta]; omega) (by dsimp [H]; omega)
        (by have := hVB
              (fkRectFaithfulShearPoint (fkRectSquareDevelopPoint pv))
              Vfaithful.start_mem_support
            dsimp [alpha, beta] at *; omega)
        (by have := hVB
              (fkRectFaithfulShearPoint (fkRectSquareDevelopPoint pv))
              Vfaithful.start_mem_support
            dsimp [alpha, beta] at *; omega)
        (by have := hVB
              (fkRectFaithfulShearPoint (fkRectSquareDevelopPoint qv))
              Vfaithful.end_mem_support
            dsimp [alpha, beta] at *; omega)
        (by have := hVB
              (fkRectFaithfulShearPoint (fkRectSquareDevelopPoint qv))
              Vfaithful.end_mem_support
            dsimp [alpha, beta] at *; omega)
        Vcross hVcrossRect hWstartRect hWendRect
        rfl rfl Wcross hWcrossRect
    apply hWcrossDisjoint z hzW
    simpa [Vcross] using hzV
  obtain ⟨z, hzW, hzV⟩ := hfaithfulIntersection
  obtain ⟨d, hdl, rd, hrd, hzd⟩ := hWfaithful z hzW
  obtain ⟨e, hel, re, hre, hze⟩ := hVfaithful z hzV
  have hde : FKRectIntegralSquareDartsIncident d e :=
    fkRectIntegralSquareDartsIncident_of_faithfulRouteSite
      d e rd re hrd hre (hzd.symm.trans hze)
  exact hRepSupp.common_of_incident R hLvSupp hdl hel hde


theorem fkRectHorizontalCylinder_support_intersects_bottomTop
    (R : FKRectTorus) (bottomX topX : Fin R.width)
    (V : (fkRectHorizontalCylinderGraph R).Walk
      (bottomX, fkRectBottomRow R) (topX, fkRectTopRow R))
    {x : R.Vertex}
    (W : (fkRectHorizontalCylinderGraph R).Walk x x)
    (hwind : (fkRectWalkWinding R W).1 ≠ 0) :
    ∃ v, v ∈ W.support ∧ v ∈ V.support := by
  rcases lt_or_gt_of_ne hwind with hneg | hpos
  · obtain ⟨v, hvW, hvV⟩ :=
      fkRectHorizontalCylinder_support_intersects_bottomTop_of_pos
        R bottomX topX V W.reverse (by
          rw [fkRectWalkWinding_reverse]
          omega)
    exact ⟨v, by simpa using hvW, hvV⟩
  · exact fkRectHorizontalCylinder_support_intersects_bottomTop_of_pos
      R bottomX topX V W hpos


end
end StatMech.FrontierD
