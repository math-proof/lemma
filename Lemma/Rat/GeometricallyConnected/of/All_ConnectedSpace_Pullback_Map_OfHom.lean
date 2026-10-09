import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
[AlgebraicGeometry_geometricallyConnected_of_forall_connectedSpace_pullback_of_isAlgClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_geometricallyConnected_of_forall_connectedSpace_pullback_of_isAlgClosed.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of R)}
-- given
  (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : R →+* k), ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x)))) :
-- imply
  GeometricallyConnected f := by
-- proof
  refine ⟨(geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms).2 fun K _ _ => ?_⟩

  let k := AlgebraicClosure K
  let x : R →+* k := (algebraMap K k).comp (algebraMap R K)
  let a : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of K) := Spec.map (CommRingCat.ofHom (algebraMap K k))
  let b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have hx : Spec.map (CommRingCat.ofHom x) = a ≫ b := by
    simp only [x, a, b, CommRingCat.ofHom_comp, Spec.map_comp]
  have hk : ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))) := h k x

  let p : pullback f (Spec.map (CommRingCat.ofHom x)) ⟶ pullback f b :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ a) (by rw [pullback.condition, hx, Category.assoc])
  have hp : IsPullback p (pullback.snd f (Spec.map (CommRingCat.ofHom x))) (pullback.snd f b) a := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f b)
    rw [pullback.lift_fst, ← hx]
    exact IsPullback.of_hasPullback f _
  have : Surjective a := by
    have : Subsingleton ↥(Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    infer_instance
  have : Surjective p := MorphismProperty.of_isPullback hp.flip inferInstance

  rw [connectedSpace_iff_univ, ← Set.range_eq_univ.mpr p.surjective]
  exact isConnected_range p.continuous


-- created on 2026-10-05
