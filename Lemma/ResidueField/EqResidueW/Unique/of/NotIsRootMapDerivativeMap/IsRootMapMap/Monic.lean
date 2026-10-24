import Mathlib
import sympy.Basic
open IsLocalRing Polynomial


/--
[HenselianLocalRing_existsUnique_isRoot_map_residue_eq_of_isRoot_of_derivative_ne_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HenselianLocalRing_existsUnique_isRoot_map_residue_eq_of_isRoot_of_derivative_ne_zero.lean)
-/
@[path]
private lemma main
  [CommRing A₀] [CommRing W] [Algebra A₀ W] [IsLocalRing W] [HenselianLocalRing W]
  {tbar : ResidueField W}
-- given
  (h : A₀[X])
  (hmonic : h.Monic)
  (hroot : ((h.map (algebraMap A₀ W)).map (IsLocalRing.residue W)).IsRoot tbar)
  (hsimple : ¬ ((h.map (algebraMap A₀ W)).derivative.map (IsLocalRing.residue W)).IsRoot tbar) :
-- imply
  ∃! t : W, (h.map (algebraMap A₀ W)).IsRoot t ∧ IsLocalRing.residue W t = tbar := by
-- proof
  classical
    set g : W[X] := h.map (algebraMap A₀ W) with hg
    have hgm : g.Monic := hmonic.map _
    have hres : ∀ (p : W[X]) (x : W),
        (p.map (IsLocalRing.residue W)).eval (IsLocalRing.residue W x) = IsLocalRing.residue W (p.eval x) := by
      intro p x; rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
    obtain ⟨a₀, ha₀⟩ := IsLocalRing.residue_surjective (R := W) tbar
    have h1 : g.eval a₀ ∈ maximalIdeal W := by
      rwa [← IsLocalRing.residue_eq_zero_iff, ← hres, ha₀]
    have h2 : IsUnit (g.derivative.eval a₀) := by
      by_contra hnu
      apply hsimple
      have : IsLocalRing.residue W (g.derivative.eval a₀) = 0 :=
        (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
      rwa [← hres, ha₀] at this
    obtain ⟨t, ht, hta⟩ := HenselianLocalRing.is_henselian g hgm a₀ h1 h2
    have htres : IsLocalRing.residue W t = tbar := by
      rwa [← ha₀, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    refine ⟨t, ⟨ht, htres⟩, ?_⟩
    rintro t' ⟨ht', ht'res⟩
    obtain ⟨k, hk⟩ := Polynomial.binomExpansion g t (t' - t)
    rw [add_sub_cancel, show g.eval t' = 0 from ht', show g.eval t = 0 from ht, zero_add] at hk
    have hfac : (t' - t) * (g.derivative.eval t + k * (t' - t)) = 0 := by
      have := hk; linear_combination (exp := 1) -this
    have hd : t' - t ∈ maximalIdeal W := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, htres, ht'res, sub_self]
    have hunit : IsUnit (g.derivative.eval t + k * (t' - t)) := by
      by_contra hnu
      apply hsimple
      have hm : g.derivative.eval t + k * (t' - t) ∈ maximalIdeal W := (IsLocalRing.mem_maximalIdeal _).mpr hnu
      have hm2 : g.derivative.eval t ∈ maximalIdeal W := by
        have := (maximalIdeal W).sub_mem hm ((maximalIdeal W).mul_mem_left k hd)
        simpa using this
      have : IsLocalRing.residue W (g.derivative.eval t) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hm2
      rwa [← hres, htres] at this
    have : t' - t = 0 := by
      have := congrArg (· * hunit.unit⁻¹.val) hfac
      simpa [mul_assoc, IsUnit.mul_val_inv] using this
    exact (sub_eq_zero.mp this)


-- created on 2026-10-23
