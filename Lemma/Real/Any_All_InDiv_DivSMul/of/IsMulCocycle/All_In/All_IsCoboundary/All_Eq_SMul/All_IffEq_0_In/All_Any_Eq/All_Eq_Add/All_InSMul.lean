import Mathlib
import sympy.Basic

open groupCohomology

/--
[groupCohomology_exists_div_mem_of_isMulCocycle1_of_presentation](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_exists_div_mem_of_isMulCocycle1_of_presentation.lean)
-/
@[main]
private lemma main
  {G M P : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M] [AddCommGroup P] [SMul G P]
  {Fn Fn1 : Subgroup M}
  {π : M → P}
  {f : G → M}
-- given
  (hstab : ∀ (g : G) (x : M), x ∈ Fn → g • x ∈ Fn)
  (hπmul : ∀ x y, x ∈ Fn → y ∈ Fn → π (x * y) = π x + π y)
  (hπsurj : ∀ p : P, ∃ x ∈ Fn, π x = p)
  (hπker : ∀ x, x ∈ Fn → (π x = 0 ↔ x ∈ Fn1))
  (hπsmul : ∀ (g : G) (x : M), x ∈ Fn → π (g • x) = g • π x)
  (hP : ∀ f : G → P, IsCocycle₁ f → IsCoboundary₁ f)
  (hfF : ∀ g, f g ∈ Fn)
  (hf : IsMulCocycle₁ f) :
-- imply
  ∃ a ∈ Fn, ∀ g, f g / (g • a / a) ∈ Fn1 := by
-- proof
  have hπdiv : ∀ x y, x ∈ Fn → y ∈ Fn → π (x / y) = π x - π y := by
    intro x y hx hy
    have h := hπmul (x / y) y (Fn.div_mem hx hy) hy
    rw [div_mul_cancel] at h
    exact eq_sub_of_add_eq h.symm
  have hc : IsCocycle₁ (fun g => π (f g)) := by
    intro g h
    simp only
    rw [hf g h, hπmul _ _ (hstab _ _ (hfF h)) (hfF g), hπsmul _ _ (hfF h)]
  obtain ⟨x, hx⟩ := hP _ hc
  obtain ⟨a, haF, rfl⟩ := hπsurj x
  refine ⟨a, haF, fun g => ?_⟩
  have hga : g • a ∈ Fn := hstab g a haF
  rw [← hπker _ (Fn.div_mem (hfF g) (Fn.div_mem hga haF)), hπdiv _ _ (hfF g) (Fn.div_mem hga haF),
    hπdiv _ _ hga haF, hπsmul _ _ haF, hx g, sub_self]


-- created on 2026-10-05
