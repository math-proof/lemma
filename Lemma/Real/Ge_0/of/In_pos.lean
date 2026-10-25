import Mathlib
import sympy.Basic
import Instance.v1.Atlas.Buildings.code.AffineCoxeter.AffineCriterion.Part2
open Finset BigOperators CoxeterGroup TitsCone


/--
[pos_root_nonneg_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineCriterion.lean)
-/
@[path]
private lemma pos_root_nonneg_coeff
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} [RootSystemData M]
  {α : B → ℝ}
  {t : B}
-- given
  (hα : α ∈ RootSystemData.Φpos (M := M)) :
-- imply
  α t ≥ 0 := by
-- proof
  by_contra h
  push Not at h
  set I := Finset.univ.erase t with hI_def
  have hI_ne : I ≠ Finset.univ := by
    intro heq; have : t ∈ I := heq ▸ Finset.mem_univ t; simp [hI_def] at this
  set x : B → ℝ := fun s => if s = t then 1 else 0
  have hx_face : x ∈ titsFaceDual M I := by
    constructor
    ·
      intro s hs
      simp [hI_def] at hs
      simp [x, hs]
    ·
      intro s hs
      simp [hI_def] at hs
      simp [x, hs]
  have ht_notin : t ∉ I := by simp [hI_def]
  have hα_ne : ∃ s, s ∉ I ∧ α s ≠ 0 := ⟨t, ht_notin, ne_of_lt h⟩
  have hpair := RootSystemData.pos_pairing_outside_span (M := M) I x hx_face α hα hα_ne
  have hpair_eq : pairing α x = α t := by
    unfold pairing
    have : ∀ s : B, α s * x s = if s = t then α t else 0 := by
      intro s; simp [x]; split <;> simp_all
    simp_rw [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  linarith [hpair_eq]

/--
[affineHyperplane_mem_titsCone_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineCriterion.lean)
-/
@[path]
private lemma affineHyperplane_mem_titsCone_of_ne_zero
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} [RootSystemData M]
  {v₀ x : B → ℝ}
-- given
  (hv₀_pos : ∀ s, v₀ s > 0)
  (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * formVal M u t = 0)
  (hAff : IsAffineCoxeter M)
  (hx : x ∈ affineHyperplane M v₀)
  (_ : x ≠ 0) :
-- imply
  x ∈ titsConeSet M := by
-- proof
  obtain ⟨p₁, p₂, t, hp₁, hp₂, ht0, ht1, hxt⟩ :=
    ChamberChasingProperty.orbit_density v₀ hv₀_pos hv₀_rad hAff x hx
  have h1t : 0 ≤ 1 - t := by linarith
  have hab : (1 - t) + t = 1 := by ring
  have hconv := titsConeSet_convex M hp₁ hp₂ h1t ht0 hab
  convert hconv using 1
  ext s
  simp [hxt s]

/--
[affine_nonposRoots_finite_of_level_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineCriterion.lean)
-/
@[path]
private lemma affine_nonposRoots_finite_of_level_bound
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} [RootSystemData M]
  {v₀ x : B → ℝ}
-- given
  (hv₀_pos : ∀ s, v₀ s > 0)
  (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * formVal M u t = 0)
  (_ : IsAffineCoxeter M)
  (hx : x ∈ affineHyperplane M v₀)
  (_ : x ≠ 0) :
-- imply
  Set.Finite (nonposRoots (RootSystemData.Φpos (M := M)) x) :=
-- proof
  RootSystemData.nonposRoots_finite_on_hyperplane v₀ hv₀_pos hv₀_rad x
    (by simpa [affineHyperplane] using hx)

/--
[affine_nuFiniteAt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineCriterion.lean)
-/
@[path]
private lemma affine_nuFiniteAt
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} [RootSystemData M]
  {v₀ x : B → ℝ}
-- given
  (hv₀_pos : ∀ s, v₀ s > 0)
  (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * formVal M u t = 0)
  (hAff : IsAffineCoxeter M)
  (hx : x ∈ affineHyperplane M v₀)
  (hx_ne : x ≠ 0) :
-- imply
  nuFiniteAt (RootSystemData.Φpos (M := M)) x :=
-- proof
  affine_nonposRoots_finite_of_level_bound hv₀_pos hv₀_rad hAff hx hx_ne

/--
[galleryChasingReflectsIntoFundClosure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineCriterion.lean)
-/
@[path]
private lemma galleryChasingReflectsIntoFundClosure
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} [RootSystemData M]
  {v₀ x : B → ℝ}
-- given
  (hv₀_pos : ∀ s, v₀ s > 0)
  (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * formVal M u t = 0)
  (hAff : IsAffineCoxeter M)
  (hx : x ∈ affineHyperplane M v₀) :
-- imply
  ∃ (ws : List B), ∀ s, (wordAction M ws x) s ≥ 0 := by
-- proof
  have hx_ne : x ≠ 0 := by
    intro hx_eq
    subst hx_eq
    simp only [affineHyperplane, Set.mem_ofPred_eq, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero] at hx
    norm_num at hx
  have hnu := affine_nuFiniteAt hv₀_pos hv₀_rad hAff hx hx_ne
  have hx_cone := nuFinite_mem_titsCone M x hx_ne hnu
  -- titsConeSet unfolds to an orbit of a fundamental-closure point
  obtain ⟨y, hy, ws, rfl⟩ := hx_cone
  refine ⟨ws.reverse, fun s => ?_⟩
  change (wordAction M ws.reverse (wordAction M ws y)) s ≥ 0
  rw [wordAction_reverse_cancel]
  exact hy s

/--
[galleryChasingOrbitDensity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineCriterion.lean)
-/
@[path]
private lemma galleryChasingOrbitDensity
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} [RootSystemData M]
  {v₀ x : B → ℝ}
-- given
  (hv₀_pos : ∀ s, v₀ s > 0)
  (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * formVal M u t = 0)
  (hAff : IsAffineCoxeter M)
  (hx : x ∈ affineHyperplane M v₀) :
-- imply
  ∃ (p₁ p₂ : B → ℝ) (t : ℝ), p₁ ∈ titsConeSet M ∧ p₂ ∈ titsConeSet M ∧ 0 ≤ t ∧ t ≤ 1 ∧ (∀ s, x s = (1 - t) * p₁ s + t * p₂ s) := by
-- proof
  obtain ⟨ws, hws⟩ := galleryChasingReflectsIntoFundClosure hv₀_pos hv₀_rad hAff hx
  have hy_fund : wordAction M ws x ∈ titsFundamentalClosure M := hws
  have hy_cone : wordAction M ws x ∈ titsConeSet M :=
    titsFundamentalClosure_subset_titsCone M hy_fund
  have hx_cone : x ∈ titsConeSet M := by
    have hrev : x = wordAction M ws.reverse (wordAction M ws x) :=
      (wordAction_reverse_cancel M ws x).symm
    rw [hrev]
    exact titsConeSet_wordAction_closed M ws.reverse _ hy_cone
  exact ⟨x, x, 0, hx_cone, hx_cone, le_refl 0, zero_le_one, fun s => by ring⟩

/--
[galleryChasingReachesTitsCone](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineCriterion.lean)
-/
@[path]
private lemma galleryChasingReachesTitsCone
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} [RootSystemData M]
  {v₀ x : B → ℝ}
-- given
  (hv₀_pos : ∀ s, v₀ s > 0)
  (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * formVal M u t = 0)
  (hAff : IsAffineCoxeter M)
  (hx : x ∈ affineHyperplane M v₀) :
-- imply
  x ∈ TitsCone.titsConeSet M := by
-- proof
  obtain ⟨p₁, p₂, t, hp₁, hp₂, ht0, ht1, hxt⟩ :=
    galleryChasingOrbitDensity hv₀_pos hv₀_rad hAff hx
  have h1t : 0 ≤ 1 - t := by linarith
  have hab : (1 - t) + t = 1 := by ring
  have hconv := titsConeSet_convex M hp₁ hp₂ h1t ht0 hab
  convert hconv using 1
  ext s
  simp [hxt s]

/--
[affineHyperplane_subset_titsCone](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineCriterion.lean)
-/
@[path]
private lemma affineHyperplane_subset_titsCone
  [DecidableEq B]
  [Fintype B]
  [Nonempty B]
  {M : CoxeterMatrix B} [RootSystemData M]
  {v₀ : B → ℝ}
-- given
  (hAff : IsAffineCoxeter M)
  (hv₀_pos : ∀ s, v₀ s > 0)
  (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * formVal M u t = 0) :
-- imply
  affineHyperplane M v₀ ⊆ titsConeSet M := by
-- proof
  intro x hx
  exact galleryChasingReachesTitsCone hv₀_pos hv₀_rad hAff hx

/--
[affineHyperplane_inter_titsCone_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineCriterion.lean)
-/
@[path]
private lemma affineHyperplane_inter_titsCone_eq
  [DecidableEq B]
  [Fintype B]
  [Nonempty B]
  {M : CoxeterMatrix B} [RootSystemData M]
  {v₀ : B → ℝ}
-- given
  (hAff : IsAffineCoxeter M)
  (hv₀_pos : ∀ s, v₀ s > 0)
  (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * formVal M u t = 0) :
-- imply
  affineHyperplane M v₀ ∩ titsConeSet M = affineHyperplane M v₀ := by
-- proof
  ext x
  constructor
  ·
    intro ⟨hx, _⟩
    exact hx
  ·
    intro hx
    exact ⟨hx, affineHyperplane_subset_titsCone hAff hv₀_pos hv₀_rad hx⟩

/--
[chamberChasingProperty_instance](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineCriterion.lean)
-/
@[path]
private lemma chamberChasingProperty_instance_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} [RootSystemData M] :
-- imply
  ChamberChasingProperty M := by
-- proof
  apply chamberChasingProperty_instance M


-- created on 2026-10-23
-- updated on 2026-10-24
