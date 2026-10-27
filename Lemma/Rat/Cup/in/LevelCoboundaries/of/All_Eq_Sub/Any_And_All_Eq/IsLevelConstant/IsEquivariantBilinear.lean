import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.GroupCohomology.ContinuousH2
import Lemma.GroupCohomology.CupProduct
import Lemma.Int.P2MUtil
open CategoryTheory groupCohomology
open Int


namespace Definitions
end Definitions

/--
[groupCohomology_cup_mem_levelCoboundaries2_of_mem_coboundaries1_right](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_cup_mem_levelCoboundaries2_of_mem_coboundaries1_right.lean)
-/
@[path]
private lemma main
  {k G : Type u} [CommRing k] [Group G]
  {r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
  {A B N : Rep.{u} k G}
  {φ : A →ₗ[k] B →ₗ[k] N}
  {f : cocycles₁ A}
  {g : cocycles₁ B}
  {b : B}
-- given
  (hφ : Rep.IsEquivariantBilinear A B N φ)
  (hf : IsLevelConstant₁ r (⇑f))
  (hb : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ ∀ s, r s ∈ F.fixingSubgroup → B.ρ s b = b)
  (hg : ∀ s, g s = B.ρ s b - b) :
-- imply
  (cup φ hφ f g : G × G → N) ∈ levelCoboundaries₂ r N := by
-- proof
  obtain ⟨Ff, hFf, hf'⟩ := hf
  obtain ⟨Fb, hFb, hb'⟩ := hb
  have : FiniteDimensional ℚ Ff := hFf
  have : FiniteDimensional ℚ Fb := hFb
  refine (mem_levelCoboundaries₂_iff r N _).2
    ⟨fun s => -(φ (f s) (B.ρ s b)),
      ⟨Ff ⊔ Fb, inferInstance, fun s u hu => ?_⟩, funext fun p => ?_⟩
  ·
    simp only
    rw [hf' s u (IntermediateField.fixingSubgroup_antitone le_sup_left hu)]
    rw [map_mul, Module.End.mul_apply]
    rw [hb' u (IntermediateField.fixingSubgroup_antitone le_sup_right hu)]
  ·
    obtain ⟨s, t⟩ := p
    rw [d₁₂_hom_apply]
    show N.ρ s (-(φ (f t) (B.ρ t b))) - -(φ (f (s * t)) (B.ρ (s * t) b)) + -(φ (f s) (B.ρ s b)) =
      φ (f s) (B.ρ s (g t))
    rw [hg t, (mem_cocycles₁_iff (⇑f)).1 f.2 s t, map_mul, Module.End.mul_apply, map_neg,
      ← hφ s (f t) (B.ρ t b)]
    simp only [map_add, map_sub, LinearMap.add_apply]
    abel


-- created on 2026-10-24
