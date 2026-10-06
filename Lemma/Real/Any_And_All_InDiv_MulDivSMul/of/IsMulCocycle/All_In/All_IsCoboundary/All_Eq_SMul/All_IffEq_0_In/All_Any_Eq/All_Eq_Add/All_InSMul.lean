import Mathlib
import sympy.Basic

open groupCohomology

/--
[groupCohomology_exists_div_mem_of_isMulCocycle2_of_presentation](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_exists_div_mem_of_isMulCocycle2_of_presentation.lean)
-/
@[main]
private lemma main
  {G M P : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M] [AddCommGroup P] [SMul G P]
  {Fn Fn1 : Subgroup M}
  {π : M → P}
  {f : G × G → M}
-- given
  (hstab : ∀ (g : G) (x : M), x ∈ Fn → g • x ∈ Fn)
  (hπmul : ∀ x y, x ∈ Fn → y ∈ Fn → π (x * y) = π x + π y)
  (hπsurj : ∀ p : P, ∃ x ∈ Fn, π x = p)
  (hπker : ∀ x, x ∈ Fn → (π x = 0 ↔ x ∈ Fn1))
  (hπsmul : ∀ (g : G) (x : M), x ∈ Fn → π (g • x) = g • π x)
  (hP : ∀ f : G × G → P, IsCocycle₂ f → IsCoboundary₂ f)
  (hfF : ∀ x, f x ∈ Fn)
  (hf : IsMulCocycle₂ f) :
-- imply
  ∃ c : G → M, (∀ g, c g ∈ Fn) ∧ ∀ g h, f (g, h) / (g • c h / c (g * h) * c g) ∈ Fn1 := by
-- proof
  have hπdiv : ∀ x y, x ∈ Fn → y ∈ Fn → π (x / y) = π x - π y := by
    intro x y hx hy
    have h := hπmul (x / y) y (Fn.div_mem hx hy) hy
    rw [div_mul_cancel] at h
    exact eq_sub_of_add_eq h.symm
  have hc : IsCocycle₂ (fun x => π (f x)) := by
    intro g h j
    simp only
    rw [← hπmul _ _ (hfF _) (hfF _), hf g h j, hπmul _ _ (hstab _ _ (hfF _)) (hfF _),
      hπsmul _ _ (hfF _)]
  obtain ⟨x, hx⟩ := hP _ hc
  choose c hcF hcπ using fun g => hπsurj (x g)
  refine ⟨c, hcF, fun g h => ?_⟩
  have h1 : g • c h / c (g * h) ∈ Fn := Fn.div_mem (hstab _ _ (hcF h)) (hcF _)
  have hden : g • c h / c (g * h) * c g ∈ Fn := Fn.mul_mem h1 (hcF g)
  rw [← hπker _ (Fn.div_mem (hfF _) hden), hπdiv _ _ (hfF _) hden, hπmul _ _ h1 (hcF g),
    hπdiv _ _ (hstab _ _ (hcF h)) (hcF _), hπsmul _ _ (hcF h), hcπ, hcπ, hcπ, hx g h, sub_self]


-- created on 2026-10-05
