import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

/--
[AlgebraicGeometry_existsUnique_comp_eq_of_universallyClosed_of_closedPoint_notMem_range](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_existsUnique_comp_eq_of_universallyClosed_of_closedPoint_notMem_range.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsLocalRing R]
  {X Xf X' T : Scheme.{u}}
  {g : X ⟶ Spec (.of R)}
  {i : Xf ⟶ X} [IsOpenImmersion i]
  {j : X' ⟶ X}
  {f : T ⟶ X} [UniversallyClosed (f ≫ g)]
-- given
  (hcover : Set.range i ∪ Set.range j = Set.univ)
  (hempty : IsLocalRing.closedPoint R ∉ Set.range (j ≫ g)) :
-- imply
  ∃! f' : T ⟶ Xf, f' ≫ i = f := by
-- proof
  have hicl : IsClosed (Set.range i)ᶜ := by
    rw [isClosed_compl_iff, ← Scheme.Hom.coe_opensRange]
    exact i.opensRange.isOpen
  have hrange : Set.range f ⊆ Set.range i := by
    by_contra hne
    obtain ⟨_, ⟨t, rfl⟩, ht⟩ := Set.not_subset.mp hne

    have hZ : IsClosed (f ⁻¹' (Set.range i)ᶜ) := hicl.preimage f.continuous
    have himg : IsClosed ((f ≫ g) '' (f ⁻¹' (Set.range i)ᶜ)) := (f ≫ g).isClosedMap _ hZ
    have hmem : IsLocalRing.closedPoint R ∈ (f ≫ g) '' (f ⁻¹' (Set.range i)ᶜ) :=
      (IsLocalRing.specializes_closedPoint ((f ≫ g) t)).mem_closed himg ⟨t, ht, rfl⟩
    obtain ⟨z, hz, hzc⟩ := hmem
    have hzj : f z ∈ Set.range j :=
      ((hcover.symm ▸ Set.mem_univ (f z) : f z ∈ Set.range i ∪ Set.range j)).resolve_left hz
    obtain ⟨x', hx'⟩ := hzj
    exact hempty ⟨x', by rw [Scheme.Hom.comp_apply, hx', ← Scheme.Hom.comp_apply, hzc]⟩
  refine ⟨IsOpenImmersion.lift i f hrange, IsOpenImmersion.lift_fac i f hrange, fun f' hf' ↦ ?_⟩
  rw [← cancel_mono i, hf', IsOpenImmersion.lift_fac]


-- created on 2026-10-05
