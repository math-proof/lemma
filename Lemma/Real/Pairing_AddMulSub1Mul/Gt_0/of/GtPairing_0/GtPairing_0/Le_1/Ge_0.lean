import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeFiniteParabolic
import Lemma.Real.Continuous_Pairing
open Finset BigOperators CoxeterGroup


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
  have h1 : (1 - t) * (∑ s : B, α s * y s) ≥ 0 :=
    mul_nonneg (by linarith) (le_of_lt hy)
  if ht_eq : t = 0 then
    rw [ht_eq]; simp; exact hy
  else
    have : t * (∑ s : B, α s * z s) > 0 :=
      mul_pos (lt_of_le_of_ne ht0 (Ne.symm ht_eq)) hz
    linarith

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
  push_neg at hc
  obtain ⟨hy, hz⟩ := hc
  have := pairing_convex_combination_pos α y z t ht0 ht1 hy hz
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
    ((nuFiniteAt_of_mem_titsCone_sdiff_zero M v₀ hv₀_pos hv₀_rad y hy).union
      (nuFiniteAt_of_mem_titsCone_sdiff_zero M v₀ hv₀_pos hv₀_rad z hz))
  intro α ⟨hα_mem, t, ht0, ht1, hpair⟩
  have h := hyperplane_meets_segment_implies_nonpos α y z t ht0 ht1 hpair
  simp only [Set.mem_union, nonposRoots, Set.mem_sep_iff]
  obtain h | h := h
  ·
    left; exact ⟨hα_mem, h⟩
  ·
    right; exact ⟨hα_mem, h⟩

end TitsCone


-- created on 2026-10-23
-- updated on 2026-10-24
