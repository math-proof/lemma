import Mathlib
import sympy.Basic

open CategoryTheory groupCohomology
open groupCohomology

/--
[groupCohomology_exists_map_eq_of_map_eq_zero_of_injective_of_surjective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_exists_map_eq_of_map_eq_zero_of_injective_of_surjective.lean)
-/

private lemma  shortExact_of_maps {k G : Type} [CommRing k] [Group G] {X : ShortComplex (Rep k G)}
    (hf : Function.Injective X.f.hom) (hg : Function.Surjective X.g.hom)
    (hfg : ∀ y : X.X₂, X.g.hom y = 0 ↔ y ∈ Set.range X.f.hom) : X.ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ((Rep.mono_iff_injective _).2 hf) ((Rep.epi_iff_surjective _).2 hg)
  refine Functor.reflects_exact_of_faithful (forget₂ (Rep k G) (ModuleCat k)) _ ?_
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  intro y
  exact hfg y
@[main]
private lemma main
  {k G : Type} [CommRing k] [Group G]
  {X₁ X₂ X₃ : Rep.{0} k G}
  {j : X₁ ⟶ X₂}
  {π : X₂ ⟶ X₃}
  {n : ℕ}
  {y : groupCohomology X₂ n}
-- given
  (hj : Function.Injective j.hom)
  (hπ : Function.Surjective π.hom)
  (hexact : ∀ y : X₂.V, π.hom y = 0 ↔ y ∈ Set.range j.hom)
  (hy : (groupCohomology.map (MonoidHom.id G) π n).hom y = 0) :
-- imply
  ∃ x : groupCohomology X₁ n, (groupCohomology.map (MonoidHom.id G) j n).hom x = y := by
-- proof
  let X : ShortComplex (Rep k G) := ShortComplex.mk j π (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro a
    exact (hexact (j.hom a)).2 ⟨a, rfl⟩)
  have hX : X.ShortExact := shortExact_of_maps hj hπ hexact
  have hex := groupCohomology.mapShortComplex₂_exact hX n
  rw [ShortComplex.moduleCat_exact_iff] at hex
  exact hex y hy


-- created on 2026-10-05
