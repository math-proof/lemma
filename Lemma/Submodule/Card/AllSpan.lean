import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[groupCohomology_natCard_eq_and_span_map_eq_top_of_addOrderOf_eq_natCard](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_natCard_eq_and_span_map_eq_top_of_addOrderOf_eq_natCard.lean)
-/
@[path]
private lemma main
  {G : Type} [Group G] [Finite G]
  (X : Rep ℤ G) (u : groupCohomology X 2) (hu : addOrderOf u = Nat.card G)
  (h5 : ∀ (S : Subgroup G) [Fintype S], Finite (groupCohomology (Rep.res S.subtype X) 2) ∧
    Nat.card (groupCohomology (Rep.res S.subtype X) 2) ≤ Fintype.card S)
  (cor : ∀ S : Subgroup G, groupCohomology (Rep.res S.subtype X) 2 →ₗ[ℤ] groupCohomology X 2)
  (hcor : ∀ (S : Subgroup G) (x : groupCohomology X 2),
    cor S ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype X)) 2).hom x) = S.index • x) :
  -- imply
  (∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype X) 2) = Fintype.card S) ∧
    (∀ S : Subgroup G, Submodule.span ℤ
      {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype X)) 2).hom u} = ⊤) := by
  -- proof
  classical
  set res : ∀ S : Subgroup G, groupCohomology X 2 → groupCohomology (Rep.res S.subtype X) 2 :=
    fun S x => (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype X)) 2).hom x with hres
  have key : ∀ (S : Subgroup G) [Fintype S], addOrderOf (res S u) = Fintype.card S ∧
      Nat.card (groupCohomology (Rep.res S.subtype X) 2) = Fintype.card S := by
    intro S _
    let _ := (h5 S).1
    have hS0 : 0 < Fintype.card S := Fintype.card_pos
    have hidx : Fintype.card S * S.index = Nat.card G := by
      have this := S.card_mul_index
      rw [Nat.card_eq_fintype_card] at this
      refine this
    have hi0 : S.index ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hidx
      refine (Nat.card_pos (α := G)).ne' hidx.symm
    have hord_nsmul : addOrderOf (S.index • u) = Fintype.card S := by
      rw [addOrderOf_nsmul' u hi0, hu, ← hidx, Nat.gcd_eq_right (dvd_mul_left S.index (Fintype.card S)),
        Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hi0)]
    have hdvd : Fintype.card S ∣ addOrderOf (res S u) := by
      rw [← hord_nsmul, ← hcor S u]
      refine addOrderOf_map_dvd (cor S).toAddMonoidHom (res S u)
    let _ : Fintype (groupCohomology (Rep.res S.subtype X) 2) := Fintype.ofFinite _
    have hle' : addOrderOf (res S u) ≤ Fintype.card S := calc
      _ ≤ Fintype.card (groupCohomology (Rep.res S.subtype X) 2) := addOrderOf_le_card_univ
      _ = Nat.card (groupCohomology (Rep.res S.subtype X) 2) := (Nat.card_eq_fintype_card).symm
      _ ≤ Fintype.card S := (h5 S).2
    have hpos : 0 < addOrderOf (res S u) := addOrderOf_pos (res S u)
    have hordeq : addOrderOf (res S u) = Fintype.card S :=
      le_antisymm hle' (Nat.le_of_dvd hpos hdvd)
    refine ⟨hordeq, le_antisymm ((h5 S).2) ?_⟩
    calc
      _ = addOrderOf (res S u) := hordeq.symm
      _ ≤ Fintype.card (groupCohomology (Rep.res S.subtype X) 2) := addOrderOf_le_card_univ
      _ = Nat.card (groupCohomology (Rep.res S.subtype X) 2) := (Nat.card_eq_fintype_card).symm
  refine ⟨fun S _ => (key S).2, fun S => ?_⟩
  let _ : Fintype S := Fintype.ofFinite S
  let _ := (h5 S).1
  obtain ⟨hord, hcard⟩ := key S
  have hzm : AddSubgroup.zmultiples (res S u) = ⊤ := by
    apply AddSubgroup.eq_top_of_card_eq
    rw [Nat.card_zmultiples, hord, hcard]
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ AddSubgroup.zmultiples (res S u) := by
    rw [hzm]
    trivial
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  refine Submodule.mem_span_singleton.mpr ⟨n, ?_⟩
  rw [← hn, ← Int.cast_smul_eq_zsmul ℤ n (res S u), Int.cast_id]


-- created on 2026-10-20
