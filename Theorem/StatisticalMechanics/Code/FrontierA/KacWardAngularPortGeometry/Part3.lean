/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
import Mathlib.Analysis.Convex.StrictConvexSpace
import Def.StatisticalMechanics.Code.FrontierA.KacWardAngularPortGeometry.Part2


namespace StatMech.FrontierA

open Set SimpleGraph

open scoped NNReal ENNReal


@[simp] theorem KWStraightLineEmbedding.norm_dartUnit
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d : G.Dart) :
    ‖embedding.dartUnit d‖ = 1 := by
  unfold KWStraightLineEmbedding.dartUnit
  rw [norm_div]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm]
  exact div_self (norm_ne_zero_iff.mpr (embedding.dartVector_ne_zero d))

theorem KWStraightLineEmbedding.dartUnit_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d : G.Dart) :
    embedding.dartUnit d ≠ 0 := by
  intro h
  have := embedding.norm_dartUnit d
  rw [h, norm_zero] at this
  norm_num at this

theorem KWStraightLineEmbedding.dartUnit_eq_iff_arg_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d e : G.Dart) :
    embedding.dartUnit d = embedding.dartUnit e ↔
      Complex.arg (embedding.vertex d.snd - embedding.vertex d.fst) =
        Complex.arg (embedding.vertex e.snd - embedding.vertex e.fst) := by
  let x := embedding.vertex d.snd - embedding.vertex d.fst
  let y := embedding.vertex e.snd - embedding.vertex e.fst
  have hx : x ≠ 0 := by
    simpa only [x] using embedding.dartVector_ne_zero d
  have hy : y ≠ 0 := by
    simpa only [y] using embedding.dartVector_ne_zero e
  unfold KWStraightLineEmbedding.dartUnit
  change x / (‖x‖ : ℂ) = y / (‖y‖ : ℂ) ↔
    Complex.arg x = Complex.arg y
  have hrayarg : SameRay ℝ x y ↔ Complex.arg x = Complex.arg y := by
    simpa only [Complex.sameRay_iff, hx, hy, false_or]
  rw [← hrayarg]
  rw [sameRay_iff_inv_norm_smul_eq_of_ne hx hy]
  simp only [div_eq_inv_mul, Complex.real_smul, Complex.ofReal_inv]

theorem KWStraightLineEmbedding.dartUnit_ne_of_outgoing
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) {d e : G.Dart}
    (hfst : d.fst = e.fst) (hne : d ≠ e) :
    embedding.dartUnit d ≠ embedding.dartUnit e := by
  intro hunit
  have harg := (embedding.dartUnit_eq_iff_arg_eq d e).mp hunit
  apply embedding.outgoing_dartAngle_ne hfst hne
  unfold KWStraightLineEmbedding.dartAngle
  rw [harg]

@[simp] theorem KWStraightLineEmbedding.dartUnit_symm
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d : G.Dart) :
    embedding.dartUnit d.symm = -embedding.dartUnit d := by
  unfold KWStraightLineEmbedding.dartUnit
  have hvec : embedding.vertex d.fst - embedding.vertex d.snd =
      -(embedding.vertex d.snd - embedding.vertex d.fst) := by ring
  change (embedding.vertex d.fst - embedding.vertex d.snd) /
      (‖embedding.vertex d.fst - embedding.vertex d.snd‖ : ℂ) =
    -((embedding.vertex d.snd - embedding.vertex d.fst) /
      (‖embedding.vertex d.snd - embedding.vertex d.fst‖ : ℂ))
  rw [hvec, norm_neg]
  ring

theorem KWStraightLineEmbedding.dartVector_eq_norm_mul_dartUnit
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d : G.Dart) :
    embedding.vertex d.snd - embedding.vertex d.fst =
      (‖embedding.vertex d.snd - embedding.vertex d.fst‖ : ℂ) *
        embedding.dartUnit d := by
  unfold KWStraightLineEmbedding.dartUnit
  have hnorm : (‖embedding.vertex d.snd - embedding.vertex d.fst‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr (embedding.dartVector_ne_zero d)
  exact (mul_div_cancel₀ _ hnorm).symm

@[simp] theorem dist_kwAngularPortVertex_owner
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (r : ℝ) (p : KWDartPort G) :
    dist (kwAngularPortVertex embedding r p) (embedding.vertex p.1) = |r| := by
  unfold kwAngularPortVertex
  rw [dist_eq_norm, add_sub_cancel_left, norm_mul,
    embedding.norm_dartUnit, mul_one]
  simp

theorem kwAngularPortVertex_sub_owner
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (r : ℝ) (p : KWDartPort G) :
    kwAngularPortVertex embedding r p - embedding.vertex p.1 =
      (r : ℂ) * embedding.dartUnit (kwDartOfPort G p) := by
  unfold kwAngularPortVertex
  ring

theorem kwAngularPortVertex_matching_sub
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (r : ℝ)
    {p q : KWDartPort G}
    (hmatching : kwDartOfPort G q = (kwDartOfPort G p).symm) :
    kwAngularPortVertex embedding r q - kwAngularPortVertex embedding r p =
      ((‖embedding.vertex (kwDartOfPort G p).snd -
          embedding.vertex (kwDartOfPort G p).fst‖ - 2 * r : ℝ) : ℂ) *
        embedding.dartUnit (kwDartOfPort G p) := by
  let d := kwDartOfPort G p
  have hp : p.1 = d.fst := (kwDartOfPort_fst G p).symm
  have hq : q.1 = d.snd := by
    calc
      q.1 = (kwDartOfPort G q).fst := (kwDartOfPort_fst G q).symm
      _ = d.symm.fst := by rw [hmatching]
      _ = d.snd := rfl
  unfold kwAngularPortVertex
  rw [hp, hq, hmatching, embedding.dartUnit_symm]
  change embedding.vertex d.snd + (r : ℂ) * -embedding.dartUnit d -
      (embedding.vertex d.fst + (r : ℂ) * embedding.dartUnit d) =
    ((‖embedding.vertex d.snd - embedding.vertex d.fst‖ - 2 * r : ℝ) : ℂ) *
      embedding.dartUnit d
  calc
    _ = (embedding.vertex d.snd - embedding.vertex d.fst) -
        (2 * r : ℝ) * embedding.dartUnit d := by push_cast; ring
    _ = (‖embedding.vertex d.snd - embedding.vertex d.fst‖ : ℂ) *
          embedding.dartUnit d - (2 * r : ℝ) * embedding.dartUnit d := by
        exact congrArg (fun z : ℂ ↦
          z - (2 * r : ℝ) * embedding.dartUnit d)
            (embedding.dartVector_eq_norm_mul_dartUnit d)
    _ = _ := by push_cast; ring


theorem kwAngularPortVertex_matching_positive
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) {r : ℝ}
    {p q : KWDartPort G}
    (hmatching : kwDartOfPort G q = (kwDartOfPort G p).symm)
    (hr : 2 * r <
      ‖embedding.vertex (kwDartOfPort G p).snd -
        embedding.vertex (kwDartOfPort G p).fst‖) :
    ∃ c : ℝ, 0 < c ∧
      kwAngularPortVertex embedding r q - kwAngularPortVertex embedding r p =
        (c : ℂ) * embedding.dartUnit (kwDartOfPort G p) := by
  refine ⟨‖embedding.vertex (kwDartOfPort G p).snd -
      embedding.vertex (kwDartOfPort G p).fst‖ - 2 * r, by linarith, ?_⟩
  exact kwAngularPortVertex_matching_sub embedding r hmatching


theorem kwAngularPortVertex_eq_iff_dartUnit_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) {r : ℝ} (hr : r ≠ 0)
    {p q : KWDartPort G} (howner : p.1 = q.1) :
    kwAngularPortVertex embedding r p = kwAngularPortVertex embedding r q ↔
      embedding.dartUnit (kwDartOfPort G p) =
        embedding.dartUnit (kwDartOfPort G q) := by
  unfold kwAngularPortVertex
  rw [howner]
  constructor
  · intro h
    have hmul : (r : ℂ) * embedding.dartUnit (kwDartOfPort G p) =
        (r : ℂ) * embedding.dartUnit (kwDartOfPort G q) := by
      exact add_left_cancel h
    exact mul_left_cancel₀ (by exact_mod_cast hr) hmul
  · intro h
    rw [h]

theorem kwAngularPortVertex_ne_of_same_owner
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) {r : ℝ} (hr : r ≠ 0)
    {p q : KWDartPort G} (howner : p.1 = q.1) (hpq : p ≠ q) :
    kwAngularPortVertex embedding r p ≠
      kwAngularPortVertex embedding r q := by
  intro heq
  have hunit := (kwAngularPortVertex_eq_iff_dartUnit_eq
    embedding hr howner).mp heq
  exact embedding.dartUnit_ne_of_outgoing
    ((kwDartOfPort_fst G p).trans
      (howner.trans (kwDartOfPort_fst G q).symm))
    ((kwDartOfPort_injective G).ne hpq) hunit

theorem KWAngularPortRadiusData.portVertex_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding) :
    Function.Injective (kwAngularPortVertex embedding (data.radius : ℝ)) := by
  intro p q heq
  by_cases howner : p.1 = q.1
  · by_contra hpq
    exact kwAngularPortVertex_ne_of_same_owner embedding
      (by exact_mod_cast data.radius_pos.ne') howner hpq heq
  · exfalso
    have hsep := data.vertex_separated p.1 q.1 howner
    have hp : dist (embedding.vertex p.1)
        (kwAngularPortVertex embedding (data.radius : ℝ) p) =
        (data.radius : ℝ) := by
      simpa only [_root_.dist_comm, abs_of_nonneg data.radius.coe_nonneg] using
        dist_kwAngularPortVertex_owner embedding (data.radius : ℝ) p
    have hq : dist (kwAngularPortVertex embedding (data.radius : ℝ) q)
        (embedding.vertex q.1) = (data.radius : ℝ) := by
      rw [dist_kwAngularPortVertex_owner]
      exact abs_of_nonneg data.radius.coe_nonneg
    have htriangle : dist (embedding.vertex p.1) (embedding.vertex q.1) ≤
        dist (embedding.vertex p.1)
            (kwAngularPortVertex embedding (data.radius : ℝ) p) +
          dist (kwAngularPortVertex embedding (data.radius : ℝ) p)
            (embedding.vertex q.1) := dist_triangle _ _ _
    rw [hp, heq, hq] at htriangle
    linarith [data.radius_pos]

theorem KWAngularPortRadiusData.portVertex_mem_sphere
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding) (p : KWDartPort G) :
    kwAngularPortVertex embedding (data.radius : ℝ) p ∈
      Metric.sphere (embedding.vertex p.1) (data.radius : ℝ) := by
  rw [Metric.mem_sphere]
  simpa only [_root_.dist_comm, abs_of_nonneg data.radius.coe_nonneg] using
    dist_kwAngularPortVertex_owner embedding (data.radius : ℝ) p

theorem kw_mem_openSegment_of_sbtw {a z b : ℂ}
    (hz : Sbtw ℝ a z b) : z ∈ openSegment ℝ a b := by
  rw [openSegment_eq_image_lineMap]
  exact (sbtw_iff_mem_image_Ioo_and_ne.mp hz).1


theorem KWAngularPortRadiusData.internalChord_mem_ball
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    {p q : KWDartPort G} (howner : p.1 = q.1) (hpq : p ≠ q)
    {z : ℂ}
    (hz : Sbtw ℝ
      (kwAngularPortVertex embedding (data.radius : ℝ) p) z
      (kwAngularPortVertex embedding (data.radius : ℝ) q)) :
    z ∈ Metric.ball (embedding.vertex p.1) (data.radius : ℝ) := by
  have hpclosed : kwAngularPortVertex embedding (data.radius : ℝ) p ∈
      Metric.closedBall (embedding.vertex p.1) (data.radius : ℝ) := by
    rw [Metric.mem_closedBall]
    exact le_of_eq (data.portVertex_mem_sphere p)
  have hqclosed : kwAngularPortVertex embedding (data.radius : ℝ) q ∈
      Metric.closedBall (embedding.vertex p.1) (data.radius : ℝ) := by
    rw [Metric.mem_closedBall]
    have hqdist : dist (kwAngularPortVertex embedding (data.radius : ℝ) q)
        (embedding.vertex q.1) = (data.radius : ℝ) :=
      data.portVertex_mem_sphere q
    rw [howner]
    exact le_of_eq hqdist
  apply openSegment_subset_ball_of_ne hpclosed hqclosed
    (data.portVertex_injective.ne hpq)
  exact kw_mem_openSegment_of_sbtw hz


theorem KWAngularPortRadiusData.internalChords_disjoint_of_owner_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    {p q p' q' : KWDartPort G}
    (hpowner : p.1 = q.1) (hpq : p ≠ q)
    (hqowner : p'.1 = q'.1) (hpq' : p' ≠ q')
    (howners : p.1 ≠ p'.1) :
    Disjoint
      {z : ℂ | Sbtw ℝ
        (kwAngularPortVertex embedding (data.radius : ℝ) p) z
        (kwAngularPortVertex embedding (data.radius : ℝ) q)}
      {z : ℂ | Sbtw ℝ
        (kwAngularPortVertex embedding (data.radius : ℝ) p') z
        (kwAngularPortVertex embedding (data.radius : ℝ) q')} := by
  rw [Set.disjoint_left]
  intro z hz hz'
  have hball := data.internalChord_mem_ball hpowner hpq hz
  have hball' := data.internalChord_mem_ball hqowner hpq' hz'
  have hsep := data.vertex_separated p.1 p'.1 howners
  have htri : dist (embedding.vertex p.1) (embedding.vertex p'.1) ≤
      dist (embedding.vertex p.1) z + dist z (embedding.vertex p'.1) :=
    dist_triangle _ _ _
  have hzlt := Metric.mem_ball'.mp hball
  have hzlt' : dist z (embedding.vertex p'.1) < (data.radius : ℝ) := by
    simpa only [_root_.dist_comm] using Metric.mem_ball'.mp hball'
  linarith

end StatMech.FrontierA
