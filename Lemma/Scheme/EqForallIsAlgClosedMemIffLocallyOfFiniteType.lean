import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma exists_point_of_isClosed
  {k : Type u} [Field k] {X : (Scheme : Type (u + 1))} (f : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType f] (x : X) (hx : IsClosed ({x} : Set X))
  (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K] :
    ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K)) ∧ p (IsLocalRing.closedPoint K) = x := by
  have hfin : IsFinite (X.fromSpecResidueField x ≫ f) := by
    rw [isClosed_singleton_iff_isClosedImmersion] at hx
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    infer_instance
  let φ : CommRingCat.of k ⟶ X.residueField x := Spec.preimage (X.fromSpecResidueField x ≫ f)
  have hφ : Spec.map φ = X.fromSpecResidueField x ≫ f := Spec.map_preimage _
  have hφfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    apply hfin
  let _ : Algebra k (X.residueField x) := φ.hom.toAlgebra
  let _ : Module.Finite k (X.residueField x) := hφfin
  let _ : Algebra.IsIntegral k (X.residueField x) := Algebra.IsIntegral.of_finite k _
  let _ : Algebra.IsAlgebraic k (X.residueField x) := Algebra.IsIntegral.isAlgebraic
  let ψ : AlgHom k (X.residueField x) K := IsAlgClosed.lift
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.fromSpecResidueField x, ?_, ?_⟩
  ·
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    congr 1
    ext r
    change ψ (φ.hom r) = algebraMap k K r
    apply ψ.commutes r
  ·
    simp only [Scheme.Hom.comp_base, TopCat.comp_app]
    apply Scheme.fromSpecResidueField_apply x _

private lemma false_of_mem_diff
  {k : Type u} [Field k] {X : (Scheme : Type (u + 1))} (f : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType f] (U V : X.Opens)
  (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (i : RingHom k K) (p : Spec (CommRingCat.of K) ⟶ X), p ≫ f = Spec.map (CommRingCat.ofHom i) → ∀ y : ↥(Spec (CommRingCat.of K)), (p.base y ∈ U ↔ p.base y ∈ V))
  (hne : ((U : Set X) ∩ ((V : Set X)ᶜ)).Nonempty) :
    False := by
  let _ : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hlc : IsLocallyClosed ((U : Set X) ∩ ((V : Set X)ᶜ)) :=
    U.isOpen.isLocallyClosed.inter V.isOpen.isClosed_compl.isLocallyClosed
  obtain ⟨x, ⟨hxU, hxV⟩, hxcl⟩ := nonempty_inter_closedPoints hne hlc
  obtain ⟨p, hpf, hpx⟩ := exists_point_of_isClosed f x hxcl (AlgebraicClosure k)
  have hiff := h (AlgebraicClosure k) (algebraMap k (AlgebraicClosure k)) p hpf (IsLocalRing.closedPoint _)
  have hpx' : p.base (IsLocalRing.closedPoint (AlgebraicClosure k)) = x := hpx
  rw [hpx'] at hiff
  apply hxV (hiff.mp hxU)

/--
[AlgebraicGeometry_Scheme_Opens_eq_of_forall_isAlgClosed_mem_iff_of_locallyOfFiniteType](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Opens_eq_of_forall_isAlgClosed_mem_iff_of_locallyOfFiniteType.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k] {X : (Scheme : Type (u + 1))} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
  (U V : X.Opens)
  (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (i : RingHom k K) (p : Spec (CommRingCat.of K) ⟶ X), p ≫ f = Spec.map (CommRingCat.ofHom i) → ∀ y : ↥(Spec (CommRingCat.of K)), (p.base y ∈ U ↔ p.base y ∈ V)) :
    U = V := by
  ext x
  constructor
  ·
    intro hxU
    by_contra hxV
    apply false_of_mem_diff f U V h ⟨x, hxU, hxV⟩
  ·
    intro hxV
    by_contra hxU
    apply false_of_mem_diff f V U (fun K _ _ i p hp y => (h K i p hp y).symm) ⟨x, hxV, hxU⟩


-- created on 2026-10-20
