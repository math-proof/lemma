import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
[AlgebraicGeometry_exists_over_hom_base_closedPoint_eq_of_isClosed_singleton](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_over_hom_base_closedPoint_eq_of_isClosed_singleton.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k] [IsAlgClosed k]
  {X : Scheme.{u}}
  {t : X ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType t]
  {x : X}
-- given
  (hx : IsClosed ({x} : Set X)) :
-- imply
  ∃ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t, z.left.base (IsLocalRing.closedPoint k) = x := by
-- proof
  refine ⟨Over.homMk (Spec.map (residueFieldIsoBase t x hx).hom ≫ X.fromSpecResidueField x) ?_, ?_⟩
  · change (Spec.map (residueFieldIsoBase t x hx).hom ≫ X.fromSpecResidueField x) ≫ t = 𝟙 _
    rw [Category.assoc, ← SpecMap_residueFieldIsoBase_inv t x hx, ← Spec.map_comp, Iso.inv_hom_id,
      Spec.map_id]
  · change (Spec.map (residueFieldIsoBase t x hx).hom ≫ X.fromSpecResidueField x).base
        (IsLocalRing.closedPoint k) = x
    have hmem : (Spec.map (residueFieldIsoBase t x hx).hom ≫ X.fromSpecResidueField x).base
        (IsLocalRing.closedPoint k) ∈ Set.range (X.fromSpecResidueField x).base :=
      ⟨(Spec.map (residueFieldIsoBase t x hx).hom).base (IsLocalRing.closedPoint k), rfl⟩
    rw [Scheme.range_fromSpecResidueField] at hmem
    exact hmem


-- created on 2026-10-05
