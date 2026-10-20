import Mathlib
import sympy.Basic
open CategoryTheory AlgebraicGeometry IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_isIso_of_isOpenImmersion_of_forall_exists_comp_eq_of_isAlgClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isIso_of_isOpenImmersion_of_forall_exists_comp_eq_of_isAlgClosed.lean)
-/
@[path]
private lemma main
  {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
  {X Y : (Scheme : Type (u + 1))} (gY : Y ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType gY] (i : X ⟶ Y) [IsOpenImmersion i]
  (hsurj : ∀ y : Spec (CommRingCat.of Ω) ⟶ Y, y ≫ gY = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) → ∃ x : Spec (CommRingCat.of Ω) ⟶ X, x ≫ i = y) :
  -- imply
  IsIso i := by
  -- proof
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨inferInstance, ⟨fun y => ?_⟩⟩
  by_contra hy
  push Not at hy
  let _ : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace gY
  have hZ : IsClosed (Set.range i.base)ᶜ := i.isOpenEmbedding.isOpen_range.isClosed_compl
  obtain ⟨z, hzZ, hzc⟩ := nonempty_inter_closedPoints (Z := (Set.range i.base)ᶜ) ⟨y, by simpa [Set.mem_compl_iff, Set.mem_range] using hy⟩ hZ.isLocallyClosed
  rw [mem_closedPoints_iff] at hzc
  have hfin : IsFinite (Y.fromSpecResidueField z ≫ gY) := by
    have := isClosed_singleton_iff_isClosedImmersion.mp hzc
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    infer_instance
  let φ : CommRingCat.of K ⟶ Y.residueField z := Spec.preimage (Y.fromSpecResidueField z ≫ gY)
  have hφ : Spec.map φ = Y.fromSpecResidueField z ≫ gY := Spec.map_preimage _
  have hφfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    apply hfin
  let _ : Algebra K (Y.residueField z) := φ.hom.toAlgebra
  let _ : Module.Finite K (Y.residueField z) := hφfin
  let _ : Algebra.IsAlgebraic K (Y.residueField z) := Algebra.IsAlgebraic.of_finite K _
  let ψ : Y.residueField z →ₐ[K] Ω := IsAlgClosed.lift
  let y' : Spec (CommRingCat.of Ω) ⟶ Y := Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Y.fromSpecResidueField z
  have hcomp : φ ≫ CommRingCat.ofHom ψ.toRingHom = CommRingCat.ofHom (algebraMap K Ω) := by
    ext a
    show ψ (φ.hom a) = algebraMap K Ω a
    apply ψ.commutes a
  have hy' : y' ≫ gY = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    apply congrArg Spec.map hcomp
  obtain ⟨x, hx⟩ := hsurj y' hy'
  apply hzZ
  refine ⟨x.base (closedPoint Ω), ?_⟩
  have h1 : i.base (x.base (closedPoint Ω)) = (x ≫ i).base (closedPoint Ω) := rfl
  rw [h1, hx]
  apply Scheme.fromSpecResidueField_apply z _


-- created on 2026-10-20
