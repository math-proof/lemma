import Mathlib
import sympy.Basic
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct


/--
[Algebra_Etale_isReduced_of_isReduced_of_isNoetherianRing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_Etale_isReduced_of_isReduced_of_isNoetherianRing.lean)
-/
private lemma geometricallyReduced_specMap
  {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.Etale R S] :
-- imply
  GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
-- proof
  constructor
  intro K _ y Z fst snd hP
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = y := ⟨Spec.preimage y, Spec.map_preimage y⟩
  let : Algebra R K := φ.hom.toAlgebra
  have hP' : IsPullback fst snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (Spec.map (CommRingCat.ofHom (algebraMap R K))) := hP
  have : _root_.IsReduced (K ⊗[R] S) :=
    Algebra.FormallyUnramified.isReduced_of_field K (K ⊗[R] S)
  have : _root_.IsReduced (S ⊗[R] K) :=
    isReduced_of_injective (Algebra.TensorProduct.comm R S K).toRingHom
      (Algebra.TensorProduct.comm R S K).injective
  have : AlgebraicGeometry.IsReduced (Spec (CommRingCat.of (S ⊗[R] K))) :=
    (affine_isReduced_iff _).mpr ‹_›
  apply isReduced_of_isOpenImmersion (Iso.trans hP'.isoPullback (pullbackSpecIso R S K)).hom

@[path]
private lemma main
  {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R] [_root_.IsReduced R] [Algebra.Etale R S] :
-- imply
  _root_.IsReduced S := by
-- proof
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    apply RingHom.flat_algebraMap_iff.mpr inferInstance
  have := geometricallyReduced_specMap (R := R) (S := S)
  apply (affine_isReduced_iff (CommRingCat.of S)).mp
  apply GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
    (Spec.map (CommRingCat.ofHom (algebraMap R S)))


-- created on 2026-10-12
