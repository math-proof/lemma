import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry

/--
[AlgebraicGeometry_eq_specMap_comp_pointOfClosedPoint_of_apply_closedPoint_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_eq_specMap_comp_pointOfClosedPoint_of_apply_closedPoint_eq.lean)
-/
@[path]
private lemma main
  {k K : Type u} [Field k] [IsAlgClosed k] [Field K]
  {ι : k →+* K}
  {X : Scheme.{u}}
  {f : X ⟶ Spec (.of k)} [LocallyOfFiniteType f]
  {p : Spec (.of K) ⟶ X}
  {x : ↥X}
-- given
  (hp : p ≫ f = Spec.map (CommRingCat.ofHom ι))
  (hx : IsClosed ({x} : Set ↥X))
  (hpx : p.base (IsLocalRing.closedPoint K) = x) :
-- imply
  p = Spec.map (CommRingCat.ofHom ι) ≫ AlgebraicGeometry.pointOfClosedPoint f x hx := by
-- proof
  subst hpx
  set e := AlgebraicGeometry.residueFieldIsoBase f (p.base (IsLocalRing.closedPoint K)) hx with he
  set φ := X.descResidueField (Scheme.stalkClosedPointTo p) with hφ
  have hdec : Spec.map φ ≫ X.fromSpecResidueField (p.base (IsLocalRing.closedPoint K)) = p :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X p

  have hφι : φ = e.hom ≫ CommRingCat.ofHom ι := by
    have h1 : Spec.map φ ≫ Spec.map e.inv = Spec.map (CommRingCat.ofHom ι) := by
      rw [AlgebraicGeometry.SpecMap_residueFieldIsoBase_inv, ← Category.assoc, hdec, hp]
    rw [← Spec.map_comp] at h1
    have h2 : e.inv ≫ φ = CommRingCat.ofHom ι := Spec.map_injective h1
    rw [← h2, Iso.hom_inv_id_assoc]
  conv_lhs => rw [← hdec, hφι, Spec.map_comp, Category.assoc]
  rfl


-- created on 2026-10-05
