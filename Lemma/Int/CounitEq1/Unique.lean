import Mathlib
import Initialize.Tactic.Attr.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v

private lemma hensSplit_isIdempotentElem_eq_zero_or_one
  {R : Type u} [CommRing R] [IsLocalRing R]
  {a : R}
  (ha : IsIdempotentElem a) :
  -- imply
  a = 0 ∨ a = 1 := by
  -- proof
  have hor := IsLocalRing.isUnit_or_isUnit_one_sub_self a
  if h : IsUnit a then
    right
    apply h.mul_left_cancel
    rw [mul_one]
    apply ha.eq
  else
    have h1 : IsUnit (1 - a) := hor.resolve_left h
    left
    apply h1.mul_left_cancel
    rw [mul_zero, sub_mul, one_mul, ha.eq, sub_self]

/--
[Bialgebra_existsUnique_counit_apply_eq_one_of_completeOrthogonalIdempotents](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Bialgebra_existsUnique_counit_apply_eq_one_of_completeOrthogonalIdempotents.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsLocalRing R]
  {H : Type v} [CommRing H] [Bialgebra R H]
  {ι : Type} [Fintype ι] (e : ι → H) (he : CompleteOrthogonalIdempotents e) :
  -- imply
  ∃! i : ι, Coalgebra.counit (R := R) (e i) = 1 := by
  -- proof
  classical
  let ε : AlgHom R H R := Bialgebra.counitAlgHom R H
  have hε : ∀ x, ε x = Coalgebra.counit x := fun x => Bialgebra.counitAlgHom_apply R H x
  have h01 : ∀ i, ε (e i) = 0 ∨ ε (e i) = 1 := fun i =>
    hensSplit_isIdempotentElem_eq_zero_or_one ((he.idem i).map ε)
  have hsum : ∑ i, ε (e i) = 1 := by
    rw [← map_sum, he.complete, map_one]
  have hex : ∃ i, ε (e i) = 1 := by
    by_contra h
    have h0 : ∀ i, ε (e i) = 0 := fun i => (h01 i).resolve_right (fun hi => h ⟨i, hi⟩)
    have hzero : ∑ i, ε (e i) = 0 := Finset.sum_eq_zero fun i _ => h0 i
    rw [hsum] at hzero
    apply one_ne_zero hzero
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, ?_, fun j hj => ?_⟩
  ·
    change Coalgebra.counit (R := R) (e i) = 1
    rw [← hε]
    apply hi
  have hj' : ε (e j) = 1 := by
    rw [hε]
    apply hj
  by_contra hne
  have h0 : e j * e i = 0 := he.ortho hne
  have h2 : ε (e j * e i) = 1 := by
    rw [map_mul, hi, hj', one_mul]
  rw [h0, map_zero] at h2
  apply zero_ne_one h2


-- created on 2026-10-20
