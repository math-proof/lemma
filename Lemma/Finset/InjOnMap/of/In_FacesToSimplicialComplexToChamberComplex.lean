import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.Building.DiscreteFibers.Part2
open Finset BigOperators


/--
[labelling_retraction_injOn_building_face](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/DiscreteFibers.lean)
-/
@[path]
lemma labelling_retraction_injOn_building_face
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {ρ : LabellingRetraction b}
  {σ : Finset V}
-- given
  (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces) :
-- imply
  Set.InjOn ρ.map ↑σ :=
-- proof
  ρ.map_injOn_face σ hσ

private lemma retraction_star_unique_preimage
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {ρ : LabellingRetraction b}
  {y : DiscreteFibers.PointF (closureSC ρ.base ρ.base_nonempty)}
  {x x' : DiscreteFibers.PointF b.toChamberComplex.toSimplicialComplex}
-- given
  (hx : ∀ v : V, DiscreteFibers.retractionMapWt ρ.map x.wt x.face v = y.wt v)
  (hx' : ∀ v : V, DiscreteFibers.retractionMapWt ρ.map x'.wt x'.face v = y.wt v)
  (hstar : x' ∈ DiscreteFibers.star x) :
-- imply
  x.wt = x'.wt := by
-- proof
  obtain ⟨σ, hσ_mem, hx_supp, hx'_supp⟩ := hstar
  have hinj : Set.InjOn ρ.map ↑σ := labelling_retraction_injOn_building_face b ρ σ hσ_mem
  funext u
  by_cases hu : u ∈ σ
  ·
    have push_eq : DiscreteFibers.retractionMapWt ρ.map x.wt x.face (ρ.map u) =
      DiscreteFibers.retractionMapWt ρ.map x'.wt x'.face (ρ.map u) := by
      rw [hx (ρ.map u), hx' (ρ.map u)]
    suffices key : ∀ (p : DiscreteFibers.PointF b.toChamberComplex.toSimplicialComplex),
      (∀ v, p.wt v ≠ 0 → v ∈ σ) →
      DiscreteFibers.retractionMapWt ρ.map p.wt p.face (ρ.map u) = p.wt u by
      rwa [← key x hx_supp, ← key x' hx'_supp]
    intro p hp_supp
    unfold DiscreteFibers.retractionMapWt
    by_cases hu_face : u ∈ p.face
    ·
      rw [Finset.sum_eq_single u]
      · simp
      · intro u' hu'_face hne
        split_ifs with hmap
        ·
          by_cases hwt : p.wt u' = 0
          · exact hwt
          · exact absurd (hinj (hp_supp u' hwt) hu hmap) hne
        · rfl
      · intro hu_abs; exact absurd hu_face hu_abs
    ·
      have hwt_zero : p.wt u = 0 := by
        by_contra h; exact hu_face (p.support_in_face u h)
      rw [hwt_zero]
      apply Finset.sum_eq_zero
      intro u' hu'_face
      split_ifs with hmap
      ·
        by_cases hwt : p.wt u' = 0
        · exact hwt
        ·
          exact absurd ((hinj (hp_supp u' hwt) hu hmap) ▸ hu'_face) hu_face
      · rfl
  ·
    have h1 : x.wt u = 0 := by
      by_contra h; exact hu (hx_supp u h)
    have h2 : x'.wt u = 0 := by
      by_contra h; exact hu (hx'_supp u h)
    rw [h1, h2]

private lemma retraction_preimage_star_contains_ball
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {ρ : LabellingRetraction b}
  {y : DiscreteFibers.PointF (closureSC ρ.base ρ.base_nonempty)} :
-- imply
  ∃ δ : ℝ, δ > 0 ∧ ∀ (x : DiscreteFibers.PointF b.toChamberComplex.toSimplicialComplex), (∀ v : V, DiscreteFibers.retractionMapWt ρ.map x.wt x.face v = y.wt v) → ∀ (z : DiscreteFibers.PointF b.toChamberComplex.toSimplicialComplex), DiscreteFibers.dist x z < δ → z ∈ DiscreteFibers.star x := by
-- proof
  have hy_face_ne : y.face.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hsum := y.wt_sum
    simp [h] at hsum
  set S := y.face.filter (fun v => 0 < y.wt v) with hS_def
  have hS_ne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hall : ∀ v ∈ y.face, y.wt v = 0 := by
      intro v hv
      have h1 := y.wt_nonneg v
      have h2 : ¬ (0 < y.wt v) := by
        intro hpos
        have hmem : v ∈ S := Finset.mem_filter.mpr ⟨hv, hpos⟩
        rw [h] at hmem; simp at hmem
      linarith
    have hzero : ∑ v ∈ y.face, y.wt v = 0 := Finset.sum_eq_zero hall
    linarith [y.wt_sum]
  set δ := S.inf' hS_ne y.wt with hδ_def
  have hδ_pos : δ > 0 := by
    obtain ⟨v₀, hv₀_mem, hv₀_eq⟩ := Finset.exists_mem_eq_inf' hS_ne y.wt
    have : δ = y.wt v₀ := by rw [hδ_def, hv₀_eq]
    rw [this]
    exact (Finset.mem_filter.mp hv₀_mem).2
  refine ⟨δ, hδ_pos, fun x hx z hdist => ?_⟩
  refine ⟨z.face, z.face_mem, ?_, fun v hv => z.support_in_face v hv⟩
  intro v hv_ne
  have hv_xface : v ∈ x.face := x.support_in_face v hv_ne
  have hinj : Set.InjOn ρ.map ↑x.face :=
    labelling_retraction_injOn_building_face b ρ x.face x.face_mem
  have hpush_v : DiscreteFibers.retractionMapWt ρ.map x.wt x.face (ρ.map v) = x.wt v := by
    unfold DiscreteFibers.retractionMapWt
    rw [Finset.sum_eq_single v]
    · simp
    · intro u' hu'_face hne
      split_ifs with hmap
      ·
        have : u' = v := by
          have h1 : (u' : V) ∈ (x.face : Set V) := Finset.mem_coe.mpr hu'_face
          have h2 : (v : V) ∈ (x.face : Set V) := Finset.mem_coe.mpr hv_xface
          exact hinj h1 h2 hmap
        exact absurd this hne
      · rfl
    · intro habs; exact absurd hv_xface habs
  have hxv_eq : x.wt v = y.wt (ρ.map v) := by rw [← hx (ρ.map v), hpush_v]
  have hxv_pos : x.wt v > 0 := by
    have h1 := x.wt_nonneg v
    obtain h | h := lt_or_eq_of_le h1
    · exact h
    · exact absurd h.symm hv_ne
  have hy_rv_pos : 0 < y.wt (ρ.map v) := hxv_eq ▸ hxv_pos
  have hrv_yface : ρ.map v ∈ y.face :=
    y.support_in_face (ρ.map v) (ne_of_gt hy_rv_pos)
  have hy_rv_ge : y.wt (ρ.map v) ≥ δ := by
    have hrv_S : ρ.map v ∈ S := Finset.mem_filter.mpr ⟨hrv_yface, hy_rv_pos⟩
    exact Finset.inf'_le y.wt hrv_S
  have hxv_ge : x.wt v ≥ δ := hxv_eq ▸ hy_rv_ge
  have hv_union : v ∈ x.face ∪ z.face := Finset.mem_union_left _ hv_xface
  have hdist_v : |x.wt v - z.wt v| ≤ DiscreteFibers.dist x z :=
    Finset.le_sup' (fun v => |x.wt v - z.wt v|) hv_union
  have habs_lt : |x.wt v - z.wt v| < x.wt v :=
    lt_of_le_of_lt hdist_v (lt_of_lt_of_le hdist hxv_ge)
  have hzv_pos : z.wt v > 0 := by
    have h1 : x.wt v - z.wt v ≤ |x.wt v - z.wt v| := le_abs_self _
    have h2 : x.wt v - z.wt v < x.wt v := lt_of_le_of_lt h1 habs_lt
    linarith
  exact z.support_in_face v (ne_of_gt hzv_pos)

private lemma retraction_preimage_discrete
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {ρ : LabellingRetraction b}
  {y : DiscreteFibers.PointF (closureSC ρ.base ρ.base_nonempty)} :
-- imply
  ∃ δ : ℝ, δ > 0 ∧ ∀ (x x' : DiscreteFibers.PointF b.toChamberComplex.toSimplicialComplex), (∀ v : V, DiscreteFibers.retractionMapWt ρ.map x.wt x.face v = y.wt v) → (∀ v : V, DiscreteFibers.retractionMapWt ρ.map x'.wt x'.face v = y.wt v) → (x.wt ≠ x'.wt → DiscreteFibers.dist x x' ≥ δ) := by
-- proof
  obtain ⟨δ, hδ_pos, hball⟩ := retraction_preimage_star_contains_ball b ρ y
  refine ⟨δ, hδ_pos, fun x x' hx hx' hneq => ?_⟩
  by_contra h_lt
  push_neg at h_lt
  have hstar : x' ∈ DiscreteFibers.star x := hball x hx x' h_lt
  have heq : x.wt = x'.wt := retraction_star_unique_preimage b ρ y x x' hx hx' hstar
  exact hneq heq


-- created on 2026-10-24
