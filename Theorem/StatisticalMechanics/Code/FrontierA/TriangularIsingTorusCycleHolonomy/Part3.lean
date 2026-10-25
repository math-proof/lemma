/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSurfaceTwist
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleHolonomy.Part3
open scoped BigOperators


namespace StatMech.FrontierA

open scoped Affine


theorem triangular_edge_eq_canonical
    (p : Int × Int) (a : Fin 6) :
    s(p, p + triangularIntStep a) =
      s(triangularCanonicalBase p a,
        triangularCanonicalBase p a +
          triangularCanonicalStep (triangularCanonicalKind a)) := by
  fin_cases a <;>
    simp [triangularIntStep, triangularCanonicalBase,
      triangularCanonicalStep, triangularCanonicalKind, Prod.ext_iff]

theorem triangular_sbtw_canonical_iff
    (p : Int × Int) (a : Fin 6) (z : Complex) :
    Sbtw Real (triangularIntPoint p) z
        (triangularIntPoint (p + triangularIntStep a)) ↔
      Sbtw Real (triangularIntPoint (triangularCanonicalBase p a)) z
        (triangularIntPoint (triangularCanonicalBase p a +
          triangularCanonicalStep (triangularCanonicalKind a))) := by
  fin_cases a <;>
    simp [triangularIntPoint, triangularIntStep, triangularCanonicalBase,
      triangularCanonicalStep, triangularCanonicalKind, sbtw_comm]

theorem triangular_canonical_open_intersection_edge_eq
    (p q : Int × Int) (a b : Fin 3) (z : Complex)
    (hp : Sbtw Real (triangularIntPoint p) z
      (triangularIntPoint (p + triangularCanonicalStep a)))
    (hq : Sbtw Real (triangularIntPoint q) z
      (triangularIntPoint (q + triangularCanonicalStep b))) :
    s(p, p + triangularCanonicalStep a) =
      s(q, q + triangularCanonicalStep b) := by
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  obtain ⟨t, ⟨ht0, ht1⟩, htz⟩ := hp.mem_image_Ioo
  obtain ⟨u, ⟨hu0, hu1⟩, huz⟩ := hq.mem_image_Ioo
  have heq : AffineMap.lineMap (triangularIntPoint (px, py))
        (triangularIntPoint ((px, py) + triangularCanonicalStep a)) t =
      AffineMap.lineMap (triangularIntPoint (qx, qy))
        (triangularIntPoint ((qx, qy) + triangularCanonicalStep b)) u :=
    htz.trans huz.symm
  have hre := congrArg Complex.re heq
  have him := congrArg Complex.im heq
  fin_cases a <;> fin_cases b <;>
    simp [triangularIntPoint, triangularCanonicalStep,
      AffineMap.lineMap_apply] at hre him ⊢
  all_goals
    try have hreCast : (px : Real) = (qx : Real) := by exact_mod_cast hre
    try have himCast : (py : Real) = (qy : Real) := by exact_mod_cast him
    have hxloR : (-2 : Real) < (qx : Real) - (px : Real) := by linarith
    have hxhiR : (qx : Real) - (px : Real) < 2 := by linarith
    have hyloR : (-2 : Real) < (qy : Real) - (py : Real) := by linarith
    have hyhiR : (qy : Real) - (py : Real) < 2 := by linarith
    have hxlo : (-2 : Int) < qx - px := by exact_mod_cast hxloR
    have hxhi : qx - px < (2 : Int) := by exact_mod_cast hxhiR
    have hylo : (-2 : Int) < qy - py := by exact_mod_cast hyloR
    have hyhi : qy - py < (2 : Int) := by exact_mod_cast hyhiR
    interval_cases hx : qx - px <;>
      interval_cases hy : qy - py <;>
      have hxR := congrArg (fun x : Int => (x : Real)) hx <;>
      have hyR := congrArg (fun x : Int => (x : Real)) hy <;>
      push_cast at hxR hyR <;>
      first
      | (exfalso; linarith)
      | omega


theorem triangular_open_intersection_edge_eq
    (p q : Int × Int) (a b : Fin 6) (z : Complex)
    (hp : Sbtw Real (triangularIntPoint p) z
      (triangularIntPoint (p + triangularIntStep a)))
    (hq : Sbtw Real (triangularIntPoint q) z
      (triangularIntPoint (q + triangularIntStep b))) :
    s(p, p + triangularIntStep a) =
      s(q, q + triangularIntStep b) := by
  rw [triangular_edge_eq_canonical p a,
    triangular_edge_eq_canonical q b]
  exact triangular_canonical_open_intersection_edge_eq
    (triangularCanonicalBase p a) (triangularCanonicalBase q b)
    (triangularCanonicalKind a) (triangularCanonicalKind b) z
    ((triangular_sbtw_canonical_iff p a z).mp hp)
    ((triangular_sbtw_canonical_iff q b z).mp hq)

theorem triangular_fin_add_two_ne_self
    {n : Nat} [NeZero n] (hn : 3 ≤ n) (i : Fin n) :
    i + 2 ≠ i := by
  intro h
  have htwo : (2 : Fin n) ≠ 0 := by
    apply Fin.ne_of_val_ne
    simp [Nat.mod_eq_of_lt (by omega : 2 < n)]
  apply htwo
  calc
    (2 : Fin n) = (i + 2) - i := by abel
    _ = i - i := by rw [h]
    _ = 0 := sub_self i

theorem triangularIntPos_vertex_not_strictly_between
    {n : Nat} [NeZero n] (direction : Fin n -> Fin 6)
    (hclosed : ∑ i, triangularIntStep (direction i) = 0)
    (hinjective : Function.Injective (triangularIntPos direction))
    (i j : Fin n) (hji : j ≠ i) (hjnext : j ≠ i + 1) :
    ¬Sbtw Real
      (triangularIntPoint (triangularIntPos direction i))
      (triangularIntPoint (triangularIntPos direction j))
      (triangularIntPoint (triangularIntPos direction (i + 1))) := by
  rw [triangularIntPos_succ direction hclosed i]
  apply triangularIntPoint_not_strictly_between_step
  · intro hpos
    exact hji (hinjective hpos)
  · intro hpos
    apply hjnext
    apply hinjective
    calc
      triangularIntPos direction j =
          triangularIntPos direction i +
            triangularIntStep (direction i) := hpos
      _ = triangularIntPos direction (i + 1) :=
        (triangularIntPos_succ direction hclosed i).symm

theorem triangularIntPos_edgeInteriors_disjoint
    {n : Nat} [NeZero n] (direction : Fin n -> Fin 6)
    (hclosed : ∑ i, triangularIntStep (direction i) = 0)
    (hn : 3 ≤ n) (hinjective : Function.Injective (triangularIntPos direction))
    (i j : Fin n) (hij : i ≠ j) :
    Disjoint
      {z : Complex | Sbtw Real
        (triangularIntPoint (triangularIntPos direction i)) z
        (triangularIntPoint (triangularIntPos direction (i + 1)))}
      {z : Complex | Sbtw Real
        (triangularIntPoint (triangularIntPos direction j)) z
        (triangularIntPoint (triangularIntPos direction (j + 1)))} := by
  apply Set.disjoint_left.2
  intro z hzi hzj
  have hedge := triangular_open_intersection_edge_eq
    (triangularIntPos direction i) (triangularIntPos direction j)
    (direction i) (direction j) z
    (by simpa [triangularIntPos_succ direction hclosed i] using hzi)
    (by simpa [triangularIntPos_succ direction hclosed j] using hzj)
  rw [Sym2.eq_iff] at hedge
  rcases hedge with hsame | hswap
  · exact hij (hinjective hsame.1)
  · have hfirst : i = j + 1 := by
      apply hinjective
      calc
        triangularIntPos direction i =
            triangularIntPos direction j +
              triangularIntStep (direction j) := hswap.1
        _ = triangularIntPos direction (j + 1) :=
          (triangularIntPos_succ direction hclosed j).symm
    have hsecond : i + 1 = j := by
      apply hinjective
      calc
        triangularIntPos direction (i + 1) =
            triangularIntPos direction i +
              triangularIntStep (direction i) :=
          triangularIntPos_succ direction hclosed i
        _ = triangularIntPos direction j := hswap.2
    apply triangular_fin_add_two_ne_self hn i
    calc
      i + 2 = (i + 1) + 1 := by
        rw [show (2 : Fin n) = 1 + 1 by
          apply Fin.ext
          simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < n),
            Nat.mod_eq_of_lt (by omega : 2 < n)], add_assoc]
      _ = j + 1 := by rw [hsecond]
      _ = i := hfirst.symm


end StatMech.FrontierA
