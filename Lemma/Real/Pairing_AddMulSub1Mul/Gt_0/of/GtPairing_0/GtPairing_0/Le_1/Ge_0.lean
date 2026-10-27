import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeFiniteParabolic.Part4
open Finset BigOperators CoxeterGroup


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
  | nil =>
    simp [sigmaWord]
  | cons s ws' ih =>
    simp only [sigmaWord, List.foldl_cons]
    rwa [sigma_fixes_radical (s := s) hv₀_rad]

end TitsCone

namespace TitsCone

/--
[dualSigmaWord_preserves_radical_pairing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeCorollary.lean)
-/
@[path]
private lemma dualSigmaWord_preserves_radical_pairing
  [DecidableEq B]
  [Fintype B]
  [Nonempty B]
  {M : CoxeterMatrix B} [RootSystemData M]
  {v₀ x : B → ℝ}
  {ws : List B}
-- given
  (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0) :
-- imply
  pairing v₀ (dualSigmaWord M ws x) = pairing v₀ x := by
-- proof
  rw [RootSystemData.pairing_word_comm]
  congr 1
  exact sigmaWord_fixes_radical (ws := ws.reverse) hv₀_rad

end TitsCone

namespace TitsCone

/--
[titsCone_sdiff_zero_radical_pairing_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeCorollary.lean)
-/
@[path]
private lemma titsCone_sdiff_zero_radical_pairing_pos
  [DecidableEq B]
  [Fintype B]
  [Nonempty B]
  {M : CoxeterMatrix B} [RootSystemData M]
  {v₀ x : B → ℝ}
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
  rw [dualSigmaWord_preserves_radical_pairing (ws := ws) (x := y) hv₀_rad]
  have hword0 : ∀ ws : List B, dualSigmaWord M ws (0 : B → ℝ) = 0 := by
    intro ws
    induction ws with
    | nil =>
      rfl
    | cons s rest ih =>
      change dualSigmaWord M rest (dualSigma M s (0 : B → ℝ)) = 0
      have h0 : dualSigma M s (0 : B → ℝ) = 0 := by
        ext t
        simp [dualSigma]
      rwa [h0]
  have hy_ne : y ≠ 0 := by
    intro h
    apply hx_ne
    subst h
    exact hword0 ws
  have ⟨s, hs⟩ : ∃ s, y s > 0 := by
    by_contra h
    simp only [not_exists, not_lt] at h
    apply hy_ne
    ext s
    simp only [Pi.zero_apply]
    have h1 := hy_nn s
    have h2 := h s
    linarith
  unfold pairing
  apply Finset.sum_pos'
  ·
    intro i _
    exact mul_nonneg (le_of_lt (hv₀_pos i)) (hy_nn i)
  ·
    exact ⟨s, Finset.mem_univ s, mul_pos (hv₀_pos s) hs⟩

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
  ·
    rintro ⟨hα, h⟩
    refine ⟨hα, ?_⟩
    have hsum : (∑ s : B, α s * (c * x s)) = c * (∑ s : B, α s * x s) := by
      rw [Finset.mul_sum]
      congr 1
      ext s
      ring
    rw [hsum] at h
    by_contra h'
    simp only [not_le] at h'
    linarith [mul_pos hc h']
  ·
    rintro ⟨hα, h⟩
    refine ⟨hα, ?_⟩
    have hsum : (∑ s : B, α s * (c * x s)) = c * (∑ s : B, α s * x s) := by
      rw [Finset.mul_sum]
      congr 1
      ext s
      ring
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
  [Nonempty B]
  {M : CoxeterMatrix B} [inst : RootSystemData M]
  {v₀ x : B → ℝ}
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
      rw [Finset.mul_sum]
      congr 1
      ext s
      ring
    rw [this]
    exact inv_mul_cancel₀ (ne_of_gt hpair)
  have hfin : Set.Finite (nonposRoots inst.Φpos x') :=
    inst.nonposRoots_finite_on_hyperplane v₀ hv₀_pos hv₀_rad x' hpair'
  rwa [show x' = fun s => c * x s from rfl, nonposRoots_pos_scale (Φ := inst.Φpos) (x := x) hc_pos] at hfin

end TitsCone

namespace TitsCone

/--
[nuFiniteAt_of_mem_titsCone_sdiff_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeCorollary.lean)
-/
@[path]
private lemma nuFiniteAt_of_mem_titsCone_sdiff_zero
  [DecidableEq B]
  [Fintype B]
  [Nonempty B]
  {M : CoxeterMatrix B} [inst : RootSystemData M]
  {v₀ x : B → ℝ}
-- given
  (hv₀_pos : ∀ s, v₀ s > 0)
  (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0)
  (hx : x ∈ titsConeSet M \ {0}) :
-- imply
  nuFiniteAt inst.Φpos x := by
-- proof
  obtain ⟨hx_cone, hx_ne⟩ := hx
  apply nuFiniteAt_of_radical_pairing_pos hv₀_pos hv₀_rad
  exact titsCone_sdiff_zero_radical_pairing_pos hv₀_pos hv₀_rad hx_cone hx_ne

end TitsCone


namespace TitsCone

/--
[pairing_convex_combination_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/LocalFiniteness.lean)
-/
@[path]
private lemma pairing_convex_combination_pos
  [DecidableEq B]
  [Fintype B]
  {α y z : B → ℝ}
  {t : ℝ}
-- given
  (ht0 : 0 ≤ t)
  (ht1 : t ≤ 1)
  (hy : pairing α y > 0)
  (hz : pairing α z > 0) :
-- imply
  pairing α (fun s => (1 - t) * y s + t * z s) > 0 := by
-- proof
  unfold pairing
  have hconv : ∑ s : B, α s * ((1 - t) * y s + t * z s) =
    (1 - t) * (∑ s : B, α s * y s) + t * (∑ s : B, α s * z s) := by
    have h : ∀ s : B, α s * ((1 - t) * y s + t * z s) =
      (1 - t) * (α s * y s) + t * (α s * z s) := fun s => by ring
    simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hconv]
  have hySum : ∑ s : B, α s * y s > 0 := by
    simpa [pairing] using hy
  have hzSum : ∑ s : B, α s * z s > 0 := by
    simpa [pairing] using hz
  have ht1' : 0 ≤ 1 - t := by linarith
  -- either t = 0 (then left term = hySum > 0) or t > 0 (right term > 0)
  if ht_eq : t = 0 then
    simp [ht_eq]
    exact hySum
  else
    have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht_eq)
    have hright : t * ∑ s : B, α s * z s > 0 := mul_pos htpos hzSum
    nlinarith

end TitsCone

namespace TitsCone

/--
[hyperplane_meets_segment_implies_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/LocalFiniteness.lean)
-/
@[path]
private lemma hyperplane_meets_segment_implies_nonpos
  [DecidableEq B]
  [Fintype B]
  {α y z : B → ℝ}
  {t : ℝ}
-- given
  (ht0 : 0 ≤ t)
  (ht1 : t ≤ 1)
  (h : pairing α (fun s => (1 - t) * y s + t * z s) = 0) :
-- imply
  pairing α y ≤ 0 ∨ pairing α z ≤ 0 := by
-- proof
  by_contra hc
  push Not at hc
  obtain ⟨hy, hz⟩ := hc
  have := pairing_convex_combination_pos (α := α) (y := y) (z := z) (t := t) ht0 ht1 hy hz
  linarith

end TitsCone

namespace TitsCone

/--
[segment_meets_finite_roots](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/LocalFiniteness.lean)
-/
@[path]
private lemma segment_meets_finite_roots
  [DecidableEq B]
  [Fintype B]
  [Nonempty B]
  {M : CoxeterMatrix B} [inst : RootSystemData M]
  {v₀ y z : B → ℝ}
-- given
  (hv₀_pos : ∀ s, v₀ s > 0)
  (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0)
  (hy : y ∈ titsConeSet M \ {0})
  (hz : z ∈ titsConeSet M \ {0}) :
-- imply
  Set.Finite {α ∈ inst.Φpos | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ pairing α (fun s => (1 - t) * y s + t * z s) = 0} := by
-- proof
  apply Set.Finite.subset
    ((nuFiniteAt_of_mem_titsCone_sdiff_zero (x := y) hv₀_pos hv₀_rad hy).union
      (nuFiniteAt_of_mem_titsCone_sdiff_zero (x := z) hv₀_pos hv₀_rad hz))
  intro α ⟨hα_mem, t, ht0, ht1, hpair⟩
  have h := hyperplane_meets_segment_implies_nonpos (α := α) (y := y) (z := z) (t := t) ht0 ht1 hpair
  simp only [Set.mem_union, nonposRoots, Set.mem_sep_iff]
  obtain h | h := h
  ·
    left; exact ⟨hα_mem, h⟩
  ·
    right; exact ⟨hα_mem, h⟩

end TitsCone


-- created on 2026-10-23
-- updated on 2026-10-26
