import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeFiniteParabolic
import Lemma.Finset.NuFiniteAt_pos.of.In_TitsFaceDual.Ne_Univ
open Finset BigOperators CoxeterGroup


namespace TitsCone

/--
[continuous_pairing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeCorollary.lean)
-/
@[path]
private lemma continuous_pairing
  [DecidableEq B]
  [Fintype B]
  {α : B → ℝ} :
-- imply
  Continuous (fun x : B → ℝ => pairing α x) := by
-- proof
  unfold pairing
  apply continuous_finset_sum
  intro s _
  exact continuous_const.mul (continuous_apply s)

end TitsCone

namespace TitsCone

/--
[isOpen_pairing_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeCorollary.lean)
-/
@[path]
private lemma isOpen_pairing_pos
  [DecidableEq B]
  [Fintype B]
  {α : B → ℝ} :
-- imply
  IsOpen {x : B → ℝ | pairing α x > 0} :=
-- proof
  isOpen_lt continuous_const (continuous_pairing α)

end TitsCone

namespace TitsCone

/--
[sigma_fixes_radical](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeCorollary.lean)
-/
@[path]
private lemma sigma_fixes_radical
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {v₀ : B → ℝ}
  {s : B}
-- given
  (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0) :
-- imply
  CoxeterGroup.sigma M s v₀ = v₀ := by
-- proof
  ext t
  simp only [CoxeterGroup.sigma, CoxeterGroup.bilinForm, CoxeterGroup.e, Pi.single_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hv₀_rad s]
  simp

end TitsCone

namespace TitsCone

/--
[sigmaWord_fixes_radical](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeCorollary.lean)
-/
@[path]
private lemma sigmaWord_fixes_radical
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {v₀ : B → ℝ}
  {ws : List B}
-- given
  (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0) :
-- imply
  sigmaWord M ws v₀ = v₀ := by
-- proof
  induction ws with
  | nil => simp [sigmaWord]
  | cons s ws' ih =>
    simp only [sigmaWord, List.foldl_cons]
    rwa [sigma_fixes_radical M v₀ hv₀_rad s]

end TitsCone

namespace TitsCone

/--
[dualSigmaWord_preserves_radical_pairing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeCorollary.lean)
-/
@[path]
private lemma dualSigmaWord_preserves_radical_pairing
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  [Nonempty B]
  [RootSystemData M]
  {v₀ : B → ℝ}
  {ws : List B}
  {x : B → ℝ}
-- given
  (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0) :
-- imply
  pairing v₀ (dualSigmaWord M ws x) = pairing v₀ x := by
-- proof
  rw [RootSystemData.pairing_word_comm]
  congr 1
  exact sigmaWord_fixes_radical M v₀ hv₀_rad ws.reverse

end TitsCone

namespace TitsCone

/--
[titsCone_sdiff_zero_radical_pairing_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeCorollary.lean)
-/
@[path]
private lemma titsCone_sdiff_zero_radical_pairing_pos
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  [Nonempty B]
  [RootSystemData M]
  {v₀ : B → ℝ}
  {x : B → ℝ}
-- given
  (hv₀_pos : ∀ s, v₀ s > 0)
  (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0)
  (hx : x ∈ titsConeSet M)
  (hx_ne : x ≠ 0) :
-- imply
  pairing v₀ x > 0 := by
-- proof
  obtain ⟨y, hy_nn, ws, hx_eq⟩ := hx
  subst hx_eq
  change pairing v₀ (dualSigmaWord M ws y) > 0
  rw [dualSigmaWord_preserves_radical_pairing M v₀ hv₀_rad ws y]
  have hy_ne : y ≠ 0 := by
    intro h; apply hx_ne; subst h
    exact wordAction_zero M ws
  have ⟨s, hs⟩ : ∃ s, y s > 0 := by
    by_contra h
    simp only [not_exists, not_lt] at h
    apply hy_ne; ext s; simp only [Pi.zero_apply]
    have h1 := hy_nn s; have h2 := h s; linarith
  unfold pairing
  apply Finset.sum_pos'
  · intro i _; exact mul_nonneg (le_of_lt (hv₀_pos i)) (hy_nn i)
  · exact ⟨s, Finset.mem_univ s, mul_pos (hv₀_pos s) hs⟩

end TitsCone

namespace TitsCone

/--
[nonposRoots_pos_scale](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeCorollary.lean)
-/
@[path]
private lemma nonposRoots_pos_scale
  [DecidableEq B]
  [Fintype B]
  {Φ : Set (B → ℝ)}
  {x : B → ℝ}
  {c : ℝ}
-- given
  (hc : c > 0) :
-- imply
  nonposRoots Φ (fun s => c * x s) = nonposRoots Φ x := by
-- proof
  ext α
  simp only [nonposRoots, Set.mem_sep_iff, pairing]
  constructor
  · rintro ⟨hα, h⟩
    refine ⟨hα, ?_⟩
    have hsum : (∑ s : B, α s * (c * x s)) = c * (∑ s : B, α s * x s) := by
      rw [Finset.mul_sum]; congr 1; ext s; ring
    rw [hsum] at h
    by_contra h'; simp only [not_le] at h'; linarith [mul_pos hc h']
  · rintro ⟨hα, h⟩
    refine ⟨hα, ?_⟩
    have hsum : (∑ s : B, α s * (c * x s)) = c * (∑ s : B, α s * x s) := by
      rw [Finset.mul_sum]; congr 1; ext s; ring
    rw [hsum]
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hc) h

end TitsCone

namespace TitsCone

/--
[nuFiniteAt_of_radical_pairing_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeCorollary.lean)
-/
@[path]
private lemma nuFiniteAt_of_radical_pairing_pos
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  [Nonempty B]
  [inst : RootSystemData M]
  {v₀ : B → ℝ}
  {x : B → ℝ}
-- given
  (hv₀_pos : ∀ s, v₀ s > 0)
  (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0)
  (hpair : pairing v₀ x > 0) :
-- imply
  nuFiniteAt inst.Φpos x := by
-- proof
  set c := (pairing v₀ x)⁻¹ with hc_def
  have hc_pos : c > 0 := inv_pos_of_pos hpair
  set x' := fun s => c * x s with hx'_def
  have hpair' : ∑ s, v₀ s * x' s = 1 := by
    simp only [hx'_def]
    have : ∑ s : B, v₀ s * (c * x s) = c * ∑ s : B, v₀ s * x s := by
      rw [Finset.mul_sum]; congr 1; ext s; ring
    rw [this]
    exact inv_mul_cancel₀ (ne_of_gt hpair)
  have hfin : Set.Finite (nonposRoots inst.Φpos x') :=
    inst.nonposRoots_finite_on_hyperplane v₀ hv₀_pos hv₀_rad x' hpair'
  rwa [show x' = fun s => c * x s from rfl, nonposRoots_pos_scale _ x c hc_pos] at hfin

end TitsCone

namespace TitsCone

/--
[titsCone_sdiff_zero_eq_radical_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeCorollary.lean)
-/
@[path]
private lemma titsCone_sdiff_zero_eq_radical_pos
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  [Nonempty B]
  [inst : RootSystemData M]
  {v₀ : B → ℝ}
-- given
  (hv₀_pos : ∀ s, v₀ s > 0)
  (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0) :
-- imply
  titsConeSet M \ {0} = {x : B → ℝ | pairing v₀ x > 0} := by
-- proof
  ext x
  simp only [Set.mem_diff, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, hne⟩
    exact titsCone_sdiff_zero_radical_pairing_pos M v₀ hv₀_pos hv₀_rad x hx hne
  · intro hpair
    have hne : x ≠ 0 := by
      intro h; rw [h] at hpair; simp [pairing] at hpair
    refine ⟨?_, hne⟩
    have hnu := nuFiniteAt_of_radical_pairing_pos M v₀ hv₀_pos hv₀_rad x hpair
    rw [titsCone_eq_zero_union_nuFinite (M := M)]
    simp only [Set.mem_union, Set.mem_setOf_eq]
    right; exact hnu

end TitsCone

namespace TitsCone

/--
[nuFiniteAt_of_mem_titsCone_sdiff_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeCorollary.lean)
-/
@[path]
private lemma nuFiniteAt_of_mem_titsCone_sdiff_zero
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  [Nonempty B]
  [inst : RootSystemData M]
  {v₀ : B → ℝ}
  {x : B → ℝ}
-- given
  (hv₀_pos : ∀ s, v₀ s > 0)
  (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0)
  (hx : x ∈ titsConeSet M \ {0}) :
-- imply
  nuFiniteAt inst.Φpos x := by
-- proof
  have hpair : pairing v₀ x > 0 := by
    have hmem : x ∈ {y : B → ℝ | pairing v₀ y > 0} :=
      (titsCone_sdiff_zero_eq_radical_pos M v₀ hv₀_pos hv₀_rad) ▸ hx
    exact hmem
  exact nuFiniteAt_of_radical_pairing_pos M v₀ hv₀_pos hv₀_rad x hpair

end TitsCone

namespace TitsCone

/--
[zeroRoots_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeCorollary.lean)
-/
@[path]
private lemma zeroRoots_finite
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  [Nonempty B]
  [inst : RootSystemData M]
  {v₀ : B → ℝ}
  {x : B → ℝ}
-- given
  (hv₀_pos : ∀ s, v₀ s > 0)
  (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0)
  (hx : x ∈ titsConeSet M \ {0}) :
-- imply
  Set.Finite {α ∈ inst.Φpos | pairing α x = 0} := by
-- proof
  apply Set.Finite.subset (nuFiniteAt_of_mem_titsCone_sdiff_zero M v₀ hv₀_pos hv₀_rad x hx)
  intro α ⟨hα, hpair⟩
  exact ⟨hα, le_of_eq hpair⟩

end TitsCone

namespace TitsCone

/--
[locallyFinite_hyperplanes_pointwise](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeCorollary.lean)
-/
@[path]
private lemma locallyFinite_hyperplanes_pointwise
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  [Nonempty B]
  [inst : RootSystemData M]
  {v₀ : B → ℝ}
  {x : B → ℝ}
-- given
  (hv₀_pos : ∀ s, v₀ s > 0)
  (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0)
  (hx : x ∈ titsConeSet M \ {0}) :
-- imply
  Set.Finite {η : Set (B → ℝ) | (∃ α ∈ inst.Φpos, η = {y : B → ℝ | pairing α y = 0}) ∧ x ∈ η} := by
-- proof
  apply Set.Finite.subset
    ((zeroRoots_finite M v₀ hv₀_pos hv₀_rad x hx).image
      (fun α => {y : B → ℝ | pairing α y = 0}))
  intro η ⟨⟨α, hα_mem, hη_eq⟩, hx_in⟩
  rw [Set.mem_image]
  refine ⟨α, ?_, hη_eq.symm⟩
  simp only [Set.mem_sep_iff]
  exact ⟨hα_mem, by rw [hη_eq] at hx_in; exact hx_in⟩

end TitsCone


-- created on 2026-10-23
-- updated on 2026-10-24
