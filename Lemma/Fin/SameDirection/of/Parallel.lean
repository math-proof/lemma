import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.Building.Infinity.SectorParallelism
open ChamberComplex AffineBuilding


/--
[Sector.Parallel.to_sameDirection](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/SectorParallelism.lean)
-/
@[path]
private lemma main
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {S₁ S₂ : Sector b}
-- given
  (h : Sector.Parallel b S₁ S₂) :
-- imply
  Sector.SameDirection b S₁ S₂ := by
-- proof
  obtain ⟨T, ⟨hT1_sub, _⟩, ⟨hT2_sub, _⟩⟩ := h
  exact ⟨T, T, hT1_sub, hT2_sub, rfl⟩



/--
[Sector.SameDirection.to_parallel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/SectorParallelism.lean)
-/
private lemma Sector.SameDirection.to_parallel
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {S₁ S₂ : Sector b}
-- given
  (h : Sector.SameDirection b S₁ S₂) :
-- imply
  Sector.Parallel b S₁ S₂ := by
-- proof
  obtain ⟨T₁, T₂, hT₁_sub, hT₂_sub, hT_eq⟩ := h
  have hT₁_subsec_S₁ : Sector.Subsector b T₁ S₁ :=
    ⟨hT₁_sub, ⟨T₁, T₁, Set.Subset.refl _, hT₁_sub, rfl⟩⟩
  have hT₁_verts_in_S₂ : T₁.vertices ⊆ S₂.vertices := by
    intro v hv
    have hv₂ : v ∈ T₂.vertices := by rw [← hT_eq]; exact hv
    exact hT₂_sub hv₂
  have hT₁_subsec_S₂ : Sector.Subsector b T₁ S₂ :=
    ⟨hT₁_verts_in_S₂, ⟨T₁, T₂, Set.Subset.refl _, hT₂_sub, hT_eq⟩⟩
  exact ⟨T₁, hT₁_subsec_S₁, hT₁_subsec_S₂⟩



/--
[same_direction_same_half_apartment_side](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/SectorParallelism.lean)
-/
private lemma same_direction_same_half_apartment_side
  {V : Type}
  [DecidableEq V]
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {S : Sector b}
  {eta : Wall b}
  {H : HalfApartment b}
  {T₁ : Sector b}
  {T₂ : Sector b}
-- given
  (heta_apt : eta.apartment = S.apartment)
  (hwall : H.wall = eta)
  (hT₁_sub : Sector.Subsector b T₁ S)
  (hT₁_in_H : ∀ v ∈ T₁.vertices, v ∈ H.vertices)
  (hT₂_sub : Sector.Subsector b T₂ S) :
-- imply
  ∃ (U : Sector b), Sector.Subsector b U T₂ ∧ ∀ v ∈ U.vertices, v ∈ H.vertices := by
-- proof
  have hvanish_func : ∀ v ∈ eta.vertices, eta.functional v = 0 := eta.functional_vanishes
  have hds := eta.functional_definite_sign S (heta_apt ▸ rfl) eta.functional hvanish_func
  have hH_canon : H.vertices = eta.halfPos ∨ H.vertices = eta.halfNeg := by
    obtain h | h := H.is_canonical
    · left; rw [← hwall]; exact h
    · right; rw [← hwall]; exact h
  have hv₀_in_S : T₁.baseVertex ∈ S.vertices := hT₁_sub.1 T₁.baseVertex_in_sector
  have hv₀_in_H : T₁.baseVertex ∈ H.vertices := hT₁_in_H T₁.baseVertex T₁.baseVertex_in_sector
  obtain h_base_le | h_le_base := hds
  ·
    have hbelow : BoundedBelowOn eta.functional S.vertices :=
      ⟨eta.functional S.baseVertex, fun z hz => h_base_le z hz⟩
    have hnot_above : ¬ BoundedAboveOn eta.functional S.vertices :=
      not_bounded_above_of_bounded_below_and_unbounded S eta heta_apt hbelow
    obtain ⟨v₁, hv₁_mem, hv₁_pos⟩ := exists_vertex_above S eta.functional hnot_above 0
    let S' : Sector b :=
      ⟨S.apartment, S.apartment_mem, v₁,
        S.vertices_in_apartment v₁ hv₁_mem,
        S.vertices, S.vertices_in_apartment,
        hv₁_mem, S.nonempty⟩
    have hds' := eta.functional_definite_sign S' (heta_apt ▸ rfl) eta.functional hvanish_func
    have h_incr : ∀ v ∈ S'.vertices, eta.functional v₁ ≤ eta.functional v := by
      obtain h_incr' | h_decr' := hds'
      · exact h_incr'
      · exfalso
        exact hnot_above ⟨eta.functional v₁, fun z hz => h_decr' z hz⟩
    have hall_pos : ∀ v ∈ S.vertices, 0 < eta.functional v := by
      intro v hv
      calc 0 < eta.functional v₁ := hv₁_pos
        _ ≤ eta.functional v := h_incr v hv
    have hall_halfPos : ∀ v ∈ S.vertices, v ∈ eta.halfPos := by
      intro v hv
      obtain hp | hn | hw := eta.sector_partition S (heta_apt ▸ rfl) v hv
      · exact hp
      · exfalso; linarith [eta.neg_nonpos v hn, hall_pos v hv]
      · exfalso; linarith [eta.functional_vanishes v hw, hall_pos v hv]
    have hv₀_halfPos : T₁.baseVertex ∈ eta.halfPos := hall_halfPos _ hv₀_in_S
    have hH_is_pos : H.vertices = eta.halfPos := by
      obtain h | h := hH_canon
      · exact h
      · exfalso
        rw [h] at hv₀_in_H
        have : eta.functional T₁.baseVertex ≤ 0 := eta.neg_nonpos _ hv₀_in_H
        linarith [hall_pos _ hv₀_in_S]
    have hT₂_in_H : ∀ v ∈ T₂.vertices, v ∈ H.vertices := by
      intro v hv
      rw [hH_is_pos]
      exact hall_halfPos v (hT₂_sub.1 hv)
    exact ⟨T₂, Sector.Subsector.refl b T₂, hT₂_in_H⟩
  ·
    have habove : BoundedAboveOn eta.functional S.vertices :=
      ⟨eta.functional S.baseVertex, fun z hz => h_le_base z hz⟩
    have hnot_below : ¬ BoundedBelowOn eta.functional S.vertices :=
      not_bounded_below_of_bounded_above_and_unbounded S eta heta_apt habove
    obtain ⟨v₁, hv₁_mem, hv₁_neg⟩ := exists_vertex_below S eta.functional hnot_below 0
    let S' : Sector b :=
      ⟨S.apartment, S.apartment_mem, v₁,
        S.vertices_in_apartment v₁ hv₁_mem,
        S.vertices, S.vertices_in_apartment,
        hv₁_mem, S.nonempty⟩
    have hds' := eta.functional_definite_sign S' (heta_apt ▸ rfl) eta.functional hvanish_func
    have h_decr : ∀ v ∈ S'.vertices, eta.functional v ≤ eta.functional v₁ := by
      obtain h_incr' | h_decr' := hds'
      · exfalso
        exact hnot_below ⟨eta.functional v₁, fun z hz => h_incr' z hz⟩
      · exact h_decr'
    have hall_neg : ∀ v ∈ S.vertices, eta.functional v < 0 := by
      intro v hv
      calc eta.functional v ≤ eta.functional v₁ := h_decr v hv
        _ < 0 := hv₁_neg
    have hall_halfNeg : ∀ v ∈ S.vertices, v ∈ eta.halfNeg := by
      intro v hv
      obtain hp | hn | hw := eta.sector_partition S (heta_apt ▸ rfl) v hv
      · exfalso; linarith [eta.pos_nonneg v hp, hall_neg v hv]
      · exact hn
      · exfalso; linarith [eta.functional_vanishes v hw, hall_neg v hv]
    have hv₀_halfNeg : T₁.baseVertex ∈ eta.halfNeg := hall_halfNeg _ hv₀_in_S
    have hH_is_neg : H.vertices = eta.halfNeg := by
      obtain h | h := hH_canon
      · exfalso
        rw [h] at hv₀_in_H
        have : 0 ≤ eta.functional T₁.baseVertex := eta.pos_nonneg _ hv₀_in_H
        linarith [hall_neg _ hv₀_in_S]
      · exact h
    have hT₂_in_H : ∀ v ∈ T₂.vertices, v ∈ H.vertices := by
      intro v hv
      rw [hH_is_neg]
      exact hall_halfNeg v (hT₂_sub.1 hv)
    exact ⟨T₂, Sector.Subsector.refl b T₂, hT₂_in_H⟩



/--
[parallel_sectors_same_positive_half_apartment](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/SectorParallelism.lean)
-/
private lemma parallel_sectors_same_positive_half_apartment
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {S₁ S₂ : Sector b}
  {eta : Wall b}
  {H : HalfApartment b}
-- given
  (hpar : Sector.SameDirection b S₁ S₂)
  (heta_apt₁ : eta.apartment = S₁.apartment)
  (heta_apt₂ : eta.apartment = S₂.apartment)
  (hpos : IsPositiveHalfApartment S₁ eta H) :
-- imply
  IsPositiveHalfApartment S₂ eta H := by
-- proof
  obtain ⟨W₁, W₂, hW₁_sub, hW₂_sub, hW_eq⟩ := hpar
  obtain ⟨hwall, T, hT_sub_S₁, hT_in_H⟩ := hpos
  have hW₁_subsector : Sector.Subsector b W₁ S₁ :=
    ⟨hW₁_sub, ⟨W₁, W₁, Set.Subset.refl _, hW₁_sub, rfl⟩⟩
  obtain ⟨U, hU_sub_W₁, hU_in_H⟩ :=
    same_direction_same_half_apartment_side b S₁ eta H heta_apt₁ hwall
      T hT_sub_S₁ hT_in_H W₁ hW₁_subsector
  have hU_verts_in_S₂ : U.vertices ⊆ S₂.vertices := by
    intro v hv
    have hv_in_W₁ : v ∈ W₁.vertices := hU_sub_W₁.1 hv
    have hv_in_W₂ : v ∈ W₂.vertices := by rw [← hW_eq]; exact hv_in_W₁
    exact hW₂_sub hv_in_W₂
  have hU_sd_S₂ : Sector.SameDirection b U S₂ := by
    exact ⟨U, U, Set.Subset.refl _, hU_verts_in_S₂, rfl⟩
  have hU_sub_S₂ : Sector.Subsector b U S₂ :=
    ⟨hU_verts_in_S₂, hU_sd_S₂⟩
  exact ⟨hwall, U, hU_sub_S₂, hU_in_H⟩



-- created on 2026-10-23
-- updated on 2026-10-26
