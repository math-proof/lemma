import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.Building.Infinity.AffineFunc.Part2
open ChamberComplex AffineBuilding


namespace AffineBuilding

/--
[Wall.pos_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/AffineFunc.lean)
-/
@[path]
lemma Wall.pos_nonneg
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {eta : Wall b} :
-- imply
  ∀ v ∈ eta.halfPos, 0 ≤ eta.functional v := by
-- proof
  intro v hv
  have hv_apt := eta.halfPos_in_apartment v hv
  exact (eta.halfPos_def v hv_apt).mp hv

end AffineBuilding

namespace AffineBuilding

/--
[Wall.neg_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/AffineFunc.lean)
-/
@[path]
lemma Wall.neg_nonpos
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {eta : Wall b} :
-- imply
  ∀ v ∈ eta.halfNeg, eta.functional v ≤ 0 := by
-- proof
  intro v hv
  have hv_apt := eta.halfNeg_in_apartment v hv
  exact (eta.halfNeg_def v hv_apt).mp hv

end AffineBuilding

namespace AffineBuilding

/--
[Wall.sector_partition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/AffineFunc.lean)
-/
@[path]
lemma Wall.sector_partition
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {eta : Wall b}
  {S : Sector b}
-- given
  (hS : S.apartment = eta.apartment) :
-- imply
  ∀ v ∈ S.vertices, v ∈ eta.halfPos ∨ v ∈ eta.halfNeg ∨ v ∈ eta.vertices := by
-- proof
  intro v hv
  have hv_apt : ∃ s ∈ eta.apartment.faces, v ∈ s := by
    have := S.vertices_in_apartment v hv
    rwa [hS] at this
  obtain h_nonneg | h_neg := le_or_gt 0 (eta.functional v)
  · left
    exact (eta.halfPos_def v hv_apt).mpr h_nonneg
  · right; left
    exact (eta.halfNeg_def v hv_apt).mpr (le_of_lt h_neg)

end AffineBuilding

namespace AffineBuilding

/--
[Wall.sector_unbounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/AffineFunc.lean)
-/
@[path]
lemma Wall.sector_unbounded
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {eta : Wall b}
  {S : Sector b}
-- given
  (hS : S.apartment = eta.apartment) :
-- imply
  ¬ ((∃ c : ℝ, ∀ z ∈ S.vertices, eta.functional z ≤ c) ∧ (∃ c : ℝ, ∀ z ∈ S.vertices, c ≤ eta.functional z)) := by
-- proof
  intro ⟨⟨c_up, hup⟩, ⟨c_lo, hlo⟩⟩
  have hM := eta.functional_unbounded_on_sectors S hS (|c_up| + |c_lo| + 1)
  obtain ⟨v, hv, hgt⟩ | ⟨v, hv, hlt⟩ := hM
  ·
    have := hup v hv
    linarith [abs_nonneg c_lo, le_abs_self c_up]
  ·
    have := hlo v hv
    linarith [abs_nonneg c_up, neg_abs_le c_lo]

end AffineBuilding

namespace AffineBuilding

/--
[sector_affine_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/AffineFunc.lean)
-/
@[path]
lemma sector_affine_decomposition
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {S : Sector b}
  {af : AffineFunctional b}
-- given
  (_haf_apt : af.apartment = S.apartment) :
-- imply
  ∃ (linear_part : V → ℝ), (∀ v ∈ S.vertices, af.toFun v = af.toFun S.baseVertex + linear_part v) ∧ linear_part S.baseVertex = 0 :=
-- proof
  ⟨fun v => af.toFun v - af.toFun S.baseVertex,
    fun v _ => by ring,
    by ring⟩

end AffineBuilding

namespace AffineBuilding

/--
[linear_part_definite_sign](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/AffineFunc.lean)
-/
@[path]
lemma linear_part_definite_sign
  {V : Type}
  [DecidableEq V]
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {S : Sector b}
  {af : AffineFunctional b}
  {eta : Wall b}
  {linear_part : V → ℝ}
-- given
  (_haf_apt : af.apartment = S.apartment)
  (heta_apt : eta.apartment = S.apartment)
  (hvanish : af.VanishesOnWall eta)
  (hdecomp : ∀ v ∈ S.vertices, af.toFun v = af.toFun S.baseVertex + linear_part v)
  (_hbase_zero : linear_part S.baseVertex = 0) :
-- imply
  (∀ v ∈ S.vertices, 0 ≤ linear_part v) ∨ (∀ v ∈ S.vertices, linear_part v ≤ 0) := by
-- proof
  have hvanish_wall : ∀ v ∈ eta.vertices, af.toFun v = 0 := hvanish.2
  have hsect_apt : S.apartment = eta.apartment := heta_apt.symm
  have hds := eta.functional_definite_sign S hsect_apt af.toFun hvanish_wall
  obtain h_ge | h_le := hds
  ·
    left
    intro v hv
    have := h_ge v hv
    have hd := hdecomp v hv
    linarith
  ·
    right
    intro v hv
    have := h_le v hv
    have hd := hdecomp v hv
    linarith

end AffineBuilding

namespace AffineBuilding

/--
[affine_functional_bounded_on_sector](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/AffineFunc.lean)
-/
@[path]
lemma affine_functional_bounded_on_sector
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {S : Sector b}
  {af : AffineFunctional b}
  {eta : Wall b}
-- given
  (haf_apt : af.apartment = S.apartment)
  (heta_apt : eta.apartment = S.apartment)
  (hvanish : af.VanishesOnWall eta) :
-- imply
  BoundedAboveOn af.toFun S.vertices ∨ BoundedBelowOn af.toFun S.vertices := by
-- proof
  obtain ⟨linear_part, hdecomp, hbase_zero⟩ :=
    sector_affine_decomposition S af haf_apt
  have hsign := linear_part_definite_sign S af eta haf_apt heta_apt hvanish
    linear_part hdecomp hbase_zero
  obtain h_nonneg | h_nonpos := hsign
  ·
    right
    exact ⟨af.toFun S.baseVertex, fun z hz => by
      rw [hdecomp z hz]
      linarith [h_nonneg z hz]⟩
  ·
    left
    exact ⟨af.toFun S.baseVertex, fun z hz => by
      rw [hdecomp z hz]
      linarith [h_nonpos z hz]⟩

end AffineBuilding

namespace AffineBuilding

/--
[wall_distance_bounded_one_side](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/AffineFunc.lean)
-/
@[path]
lemma wall_distance_bounded_one_side
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {S : Sector b}
  {eta : Wall b}
-- given
  (heta_apt : eta.apartment = S.apartment) :
-- imply
  ∃ (af : AffineFunctional b) (H₁ H₂ : HalfApartment b), af.VanishesOnWall eta ∧ H₁.wall = eta ∧ H₂.wall = eta ∧ DistBoundedInHalfApartment af eta S H₁ ∧ DistUnboundedInHalfApartment af eta S H₂ := by
-- proof
  let af : AffineFunctional b :=
    ⟨eta.apartment, eta.apartment_mem, eta.functional, eta.affineComb, eta.functionalIsAffine⟩
  have haf_apt : af.apartment = S.apartment := heta_apt
  have hvanish : af.VanishesOnWall eta := ⟨rfl, eta.functional_vanishes⟩
  have hbound := affine_functional_bounded_on_sector b S af eta haf_apt heta_apt hvanish
  have hnot_both : ¬ (BoundedAboveOn af.toFun S.vertices ∧ BoundedBelowOn af.toFun S.vertices) :=
    eta.sector_unbounded S (heta_apt ▸ rfl)
  let Hpos : HalfApartment b :=
    ⟨eta.apartment, eta.apartment_mem, eta, rfl, eta.halfPos, eta.halfPos_in_apartment, Or.inl rfl⟩
  let Hneg : HalfApartment b :=
    ⟨eta.apartment, eta.apartment_mem, eta, rfl, eta.halfNeg, eta.halfNeg_in_apartment, Or.inr rfl⟩
  have hHpos_wall : Hpos.wall = eta := rfl
  have hHneg_wall : Hneg.wall = eta := rfl
  have hpos_nonneg : ∀ v ∈ Hpos.vertices, 0 ≤ af.toFun v := eta.pos_nonneg
  have hneg_nonpos : ∀ v ∈ Hneg.vertices, af.toFun v ≤ 0 := eta.neg_nonpos
  have hpart : ∀ v ∈ S.vertices, v ∈ Hpos.vertices ∨ v ∈ Hneg.vertices ∨ v ∈ eta.vertices :=
    eta.sector_partition S (heta_apt ▸ rfl)
  obtain h_above | h_below := hbound
  ·
    obtain ⟨c_up, hc_up⟩ := h_above
    have h_not_below : ¬ BoundedBelowOn af.toFun S.vertices := by
      intro h_below_too
      exact hnot_both ⟨⟨c_up, hc_up⟩, h_below_too⟩
    refine ⟨af, Hpos, Hneg, hvanish, hHpos_wall, hHneg_wall, ?_, ?_⟩
    ·
      refine ⟨|c_up|, fun v hv hv_Hpos => ?_⟩
      unfold distToWall signedDistToWall
      have h1 : 0 ≤ af.toFun v := hpos_nonneg v hv_Hpos
      have h2 : af.toFun v ≤ c_up := hc_up v hv
      rw [abs_of_nonneg h1]
      exact le_trans h2 (le_abs_self c_up)
    ·
      intro ⟨M, hM⟩
      apply h_not_below
      refine ⟨-(|M| + 1), fun v hv => ?_⟩
      obtain hv_pos | hv_neg | hv_wall := hpart v hv
      ·
        linarith [hpos_nonneg v hv_pos, abs_nonneg M]
      ·
        have hd := hM v hv hv_neg
        unfold distToWall signedDistToWall at hd
        have h_neg_abs := neg_abs_le (af.toFun v)
        have h_abs_M := le_abs_self M
        linarith
      ·
        have := hvanish.2 v hv_wall
        linarith [abs_nonneg M]
  ·
    obtain ⟨c_lo, hc_lo⟩ := h_below
    have h_not_above : ¬ BoundedAboveOn af.toFun S.vertices := by
      intro h_above_too
      exact hnot_both ⟨h_above_too, ⟨c_lo, hc_lo⟩⟩
    refine ⟨af, Hneg, Hpos, hvanish, hHneg_wall, hHpos_wall, ?_, ?_⟩
    ·
      refine ⟨|c_lo|, fun v hv hv_Hneg => ?_⟩
      unfold distToWall signedDistToWall
      have h1 : af.toFun v ≤ 0 := hneg_nonpos v hv_Hneg
      have h2 : c_lo ≤ af.toFun v := hc_lo v hv
      rw [abs_of_nonpos h1]
      linarith [neg_abs_le c_lo]
    ·
      intro ⟨M, hM⟩
      apply h_not_above
      refine ⟨|M| + 1, fun v hv => ?_⟩
      obtain hv_pos | hv_neg | hv_wall := hpart v hv
      ·
        have hd := hM v hv hv_pos
        unfold distToWall signedDistToWall at hd
        rw [abs_of_nonneg (hpos_nonneg v hv_pos)] at hd
        have h_abs_M := le_abs_self M
        linarith
      ·
        linarith [hneg_nonpos v hv_neg, abs_nonneg M]
      ·
        have := hvanish.2 v hv_wall
        linarith [abs_nonneg M]

end AffineBuilding

namespace AffineBuilding

/--
[not_bounded_above_of_bounded_below_and_unbounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/AffineFunc.lean)
-/
@[path]
lemma not_bounded_above_of_bounded_below_and_unbounded
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {S : Sector b}
  {eta : Wall b}
-- given
  (heta_apt : eta.apartment = S.apartment)
  (hbelow : BoundedBelowOn eta.functional S.vertices) :
-- imply
  ¬ BoundedAboveOn eta.functional S.vertices := by
-- proof
  intro habove
  exact eta.sector_unbounded S (heta_apt ▸ rfl) ⟨habove, hbelow⟩

end AffineBuilding

namespace AffineBuilding

/--
[not_bounded_below_of_bounded_above_and_unbounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/AffineFunc.lean)
-/
@[path]
lemma not_bounded_below_of_bounded_above_and_unbounded
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {S : Sector b}
  {eta : Wall b}
-- given
  (heta_apt : eta.apartment = S.apartment)
  (habove : BoundedAboveOn eta.functional S.vertices) :
-- imply
  ¬ BoundedBelowOn eta.functional S.vertices := by
-- proof
  intro hbelow
  exact eta.sector_unbounded S (heta_apt ▸ rfl) ⟨habove, hbelow⟩

end AffineBuilding

namespace AffineBuilding

/--
[exists_vertex_above](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/AffineFunc.lean)
-/
@[path]
lemma exists_vertex_above
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {S : Sector b}
  {f : V → ℝ}
  {M : ℝ}
-- given
  (hnot_above : ¬ BoundedAboveOn f S.vertices) :
-- imply
  ∃ v ∈ S.vertices, M < f v := by
-- proof
  by_contra h
  push_neg at h
  exact hnot_above ⟨M, h⟩

end AffineBuilding

namespace AffineBuilding

/--
[exists_vertex_below](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/AffineFunc.lean)
-/
@[path]
lemma exists_vertex_below
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {S : Sector b}
  {f : V → ℝ}
  {M : ℝ}
-- given
  (hnot_below : ¬ BoundedBelowOn f S.vertices) :
-- imply
  ∃ v ∈ S.vertices, f v < M := by
-- proof
  by_contra h
  push_neg at h
  exact hnot_below ⟨M, h⟩

end AffineBuilding

namespace AffineBuilding

/--
[sector_subsector_in_half_apartment](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/AffineFunc.lean)
-/
@[path]
lemma sector_subsector_in_half_apartment
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {S : Sector b}
  {eta : Wall b}
-- given
  (heta_apt : eta.apartment = S.apartment) :
-- imply
  ∃ (H : HalfApartment b) (S' : Sector b), H.wall = eta ∧ Sector.Subsector b S' S ∧ ∀ v ∈ S'.vertices, v ∈ H.vertices := by
-- proof
  have hvanish_func : ∀ v ∈ eta.vertices, eta.functional v = 0 :=
    eta.functional_vanishes
  have hds := eta.functional_definite_sign S (heta_apt ▸ rfl) eta.functional hvanish_func
  obtain h_base_le | h_le_base := hds
  ·
    have hbelow : BoundedBelowOn eta.functional S.vertices :=
      ⟨eta.functional S.baseVertex, fun z hz => h_base_le z hz⟩
    have hnot_above : ¬ BoundedAboveOn eta.functional S.vertices :=
      not_bounded_above_of_bounded_below_and_unbounded S eta heta_apt hbelow
    obtain ⟨v₀, hv₀_mem, hv₀_pos⟩ := exists_vertex_above S eta.functional hnot_above 0
    let S' : Sector b :=
      ⟨S.apartment, S.apartment_mem, v₀,
        S.vertices_in_apartment v₀ hv₀_mem,
        S.vertices, S.vertices_in_apartment,
        hv₀_mem, S.nonempty⟩
    have hds' := eta.functional_definite_sign S' (heta_apt ▸ rfl) eta.functional hvanish_func
    have hS'_verts : S'.vertices = S.vertices := rfl
    have h_incr : ∀ v ∈ S'.vertices, eta.functional v₀ ≤ eta.functional v := by
      obtain h_incr' | h_decr' := hds'
      · exact h_incr'
      ·
        exfalso
        have habove : BoundedAboveOn eta.functional S.vertices :=
          ⟨eta.functional v₀, fun z hz => h_decr' z hz⟩
        exact hnot_above habove
    have hall_pos : ∀ v ∈ S'.vertices, 0 < eta.functional v := by
      intro v hv
      calc 0 < eta.functional v₀ := hv₀_pos
        _ ≤ eta.functional v := h_incr v hv
    have hall_halfPos : ∀ v ∈ S'.vertices, v ∈ eta.halfPos := by
      intro v hv
      have hv_in_S : v ∈ S.vertices := hv
      obtain hp | hn | hw := eta.sector_partition S (heta_apt ▸ rfl) v hv_in_S
      · exact hp
      ·
        exfalso; linarith [eta.neg_nonpos v hn, hall_pos v hv]
      ·
        exfalso; linarith [eta.functional_vanishes v hw, hall_pos v hv]
    let Hpos : HalfApartment b :=
      ⟨eta.apartment, eta.apartment_mem, eta, rfl, eta.halfPos, eta.halfPos_in_apartment, Or.inl rfl⟩
    exact ⟨Hpos, S', rfl, ⟨Set.Subset.refl _, Sector.SameDirection.refl b S⟩, hall_halfPos⟩
  ·
    have habove : BoundedAboveOn eta.functional S.vertices :=
      ⟨eta.functional S.baseVertex, fun z hz => h_le_base z hz⟩
    have hnot_below : ¬ BoundedBelowOn eta.functional S.vertices :=
      not_bounded_below_of_bounded_above_and_unbounded S eta heta_apt habove
    obtain ⟨v₀, hv₀_mem, hv₀_neg⟩ := exists_vertex_below S eta.functional hnot_below 0
    let S' : Sector b :=
      ⟨S.apartment, S.apartment_mem, v₀,
        S.vertices_in_apartment v₀ hv₀_mem,
        S.vertices, S.vertices_in_apartment,
        hv₀_mem, S.nonempty⟩
    have hds' := eta.functional_definite_sign S' (heta_apt ▸ rfl) eta.functional hvanish_func
    have h_decr : ∀ v ∈ S'.vertices, eta.functional v ≤ eta.functional v₀ := by
      obtain h_incr' | h_decr' := hds'
      ·
        exfalso
        have hbelow : BoundedBelowOn eta.functional S.vertices :=
          ⟨eta.functional v₀, fun z hz => h_incr' z hz⟩
        exact hnot_below hbelow
      · exact h_decr'
    have hall_neg : ∀ v ∈ S'.vertices, eta.functional v < 0 := by
      intro v hv
      calc eta.functional v ≤ eta.functional v₀ := h_decr v hv
        _ < 0 := hv₀_neg
    have hall_halfNeg : ∀ v ∈ S'.vertices, v ∈ eta.halfNeg := by
      intro v hv
      have hv_in_S : v ∈ S.vertices := hv
      obtain hp | hn | hw := eta.sector_partition S (heta_apt ▸ rfl) v hv_in_S
      ·
        exfalso; linarith [eta.pos_nonneg v hp, hall_neg v hv]
      · exact hn
      ·
        exfalso; linarith [eta.functional_vanishes v hw, hall_neg v hv]
    let Hneg : HalfApartment b :=
      ⟨eta.apartment, eta.apartment_mem, eta, rfl, eta.halfNeg, eta.halfNeg_in_apartment, Or.inr rfl⟩
    exact ⟨Hneg, S', rfl, ⟨Set.Subset.refl _, Sector.SameDirection.refl b S⟩, hall_halfNeg⟩

end AffineBuilding

namespace AffineBuilding

/--
[exists_positive_half_apartment](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/AffineFunc.lean)
-/
@[path]
lemma exists_positive_half_apartment
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {S : Sector b}
  {eta : Wall b}
-- given
  (heta_apt : eta.apartment = S.apartment) :
-- imply
  ∃ H : HalfApartment b, IsPositiveHalfApartment S eta H := by
-- proof
  obtain ⟨H, S', hwall, hsubsec, hcontain⟩ :=
    sector_subsector_in_half_apartment b S eta heta_apt
  exact ⟨H, hwall, S', hsubsec, hcontain⟩

end AffineBuilding


-- created on 2026-10-23
