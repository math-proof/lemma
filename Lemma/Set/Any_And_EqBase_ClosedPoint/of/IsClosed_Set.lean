import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

/--
[AlgebraicGeometry_Scheme_exists_SpecMap_comp_eq_of_isAlgClosed_of_isClosed_singleton](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_SpecMap_comp_eq_of_isAlgClosed_of_isClosed_singleton.lean)
-/
@[main]
private lemma main
  {k₀ : Type u} [Field k₀]
  {F : Scheme.{u}}
  {f : F ⟶ Spec (CommRingCat.of k₀)} [LocallyOfFiniteType f]
  {k : Type u} [Field k] [Algebra k₀ k] [IsAlgClosed k]
  {y : F}
-- given
  (hy : IsClosed ({y} : Set F)) :
-- imply
  ∃ z : Spec (CommRingCat.of k) ⟶ F,
      z ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k₀ k)) ∧ z.base (IsLocalRing.closedPoint k) = y := by
-- proof
  set g := F.fromSpecResidueField y ≫ f with hg
  have hfin : IsFinite g := by
    have := isClosed_singleton_iff_isClosedImmersion.mp hy
    exact (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace (f := g)).mpr inferInstance
  let φ : CommRingCat.of k₀ ⟶ F.residueField y := Spec.preimage g
  have hφ : Spec.map φ = g := Spec.map_preimage g
  have hint : φ.hom.IsIntegral := by
    rw [← IsIntegralHom.SpecMap_iff, hφ]
    infer_instance
  let : Algebra k₀ (F.residueField y) := φ.hom.toAlgebra
  have : Algebra.IsIntegral k₀ (F.residueField y) := ⟨hint⟩

  let ψ : F.residueField y →ₐ[k₀] k := IsAlgClosed.lift
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ F.fromSpecResidueField y, ?_, ?_⟩
  · rw [Category.assoc, ← hg, ← hφ, ← Spec.map_comp]
    congr 1
    ext a
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply]
    exact ψ.commutes a
  · have hmem : (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ F.fromSpecResidueField y).base
        (IsLocalRing.closedPoint k) ∈ Set.range (F.fromSpecResidueField y).base :=
      ⟨(Spec.map (CommRingCat.ofHom ψ.toRingHom)).base (IsLocalRing.closedPoint k), rfl⟩
    rw [Scheme.range_fromSpecResidueField] at hmem
    exact hmem


-- created on 2026-10-05
