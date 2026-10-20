import Mathlib
import sympy.Basic
open CategoryTheory AlgebraicGeometry Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_isFinite_of_finite_setOf_exists_section_of_isAlgClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isFinite_of_finite_setOf_exists_section_of_isAlgClosed.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k] [IsAlgClosed k] {X : (Scheme : Type (u + 1))} (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f]
  (hfin : {x : X | ∃ s : Spec (.of k) ⟶ X, s ≫ f = 𝟙 _ ∧ s (IsLocalRing.closedPoint k) = x}.Finite) :
  -- imply
  IsFinite f := by
  -- proof
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hsub : closedPoints X ⊆
    {x : X | ∃ s : Spec (.of k) ⟶ X, s ≫ f = 𝟙 _ ∧ s (IsLocalRing.closedPoint k) = x} :=
    fun x hx => ⟨pointOfClosedPoint f x hx, pointOfClosedPoint_comp f x hx,
      pointOfClosedPoint_apply f x hx _⟩
  have : DiscreteTopology X := JacobsonSpace.discreteTopology (hfin.subset hsub)
  have : Finite X :=
    Set.finite_univ_iff.mp (closedPoints_eq_univ (X := X) ▸ hfin.subset hsub)
  have hqf : LocallyQuasiFinite f :=
    LocallyQuasiFinite.of_finite_preimage_singleton f fun _ => Set.toFinite _
  have hq : RingHom.QuasiFinite (f.appTop).hom :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyQuasiFinite)).mp hqf
  refine (HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mpr ⟨inferInstance, ?_⟩
  have : IsArtinianRing ((Spec (CommRingCat.of k)).presheaf.obj (Opposite.op (⊤ : (Spec (CommRingCat.of k)).Opens))) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.isArtinianRing
  algebraize [(f.appTop).hom]
  apply Module.Finite.of_quasiFinite


-- created on 2026-10-20
