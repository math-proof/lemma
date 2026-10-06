import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

/--
[AlgebraicGeometry_exists_baseChange_chart_isPullback_of_isPullback](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_baseChange_chart_isPullback_of_isPullback.lean)
-/
@[main]
private lemma main
  {O K Q : Type u} [CommRing O] [CommRing K] [CommRing Q] [Algebra O Q] [Algebra O K]
  {X XK : Scheme.{u}}
  {toO : X ⟶ Spec (CommRingCat.of O)}
  {toK : XK ⟶ Spec (CommRingCat.of K)}
  {pr : XK ⟶ X}
  {U : X.Opens}
  {f : (U : Scheme.{u}) ⟶ Spec (CommRingCat.of Q)}
-- given
  (hpr : IsPullback pr toK toO (Spec.map (CommRingCat.ofHom (algebraMap O K))))
  (hover : f ≫ Spec.map (CommRingCat.ofHom (algebraMap O Q)) = U.ι ≫ toO) :
-- imply
  ∃ fK : ((pr ⁻¹ᵁ U : XK.Opens) : Scheme.{u}) ⟶ Spec (CommRingCat.of (K ⊗[O] Q)),
      fK ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R :=
-- proof
  O) (A := K) (B := Q)).toRingHom) = (pr ∣_ U) ≫ f ∧
       fK ≫ Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[O] Q))) = (pr ⁻¹ᵁ U).ι ≫ toK ∧
       IsPullback fK (pr ∣_ U) (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := O) (A := K) (B := Q)).toRingHom)) f := by
   have t : IsPullback (Spec.map (CommRingCat.ofHom (S := K ⊗[O] Q) Algebra.TensorProduct.includeLeftRingHom))
       (Spec.map (CommRingCat.ofHom (S := K ⊗[O] Q) (Algebra.TensorProduct.includeRight (R := O) (A := K) (B := Q)).toRingHom))
       (Spec.map (CommRingCat.ofHom (algebraMap O K))) (Spec.map (CommRingCat.ofHom (algebraMap O Q))) :=
     isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct O K Q)
   have s : IsPullback ((pr ⁻¹ᵁ U).ι ≫ toK) (pr ∣_ U) (Spec.map (CommRingCat.ofHom (algebraMap O K)))
       (f ≫ Spec.map (CommRingCat.ofHom (algebraMap O Q))) := by
     rw [hover]
     exact (isPullback_morphismRestrict pr U).flip.paste_horiz hpr.flip
   refine ⟨t.lift ((pr ⁻¹ᵁ U).ι ≫ toK) ((pr ∣_ U) ≫ f) (by rw [s.w, Category.assoc]), t.lift_snd _ _ _, ?_,
     IsPullback.of_right' s t⟩
   show t.lift _ _ _ ≫ Spec.map (CommRingCat.ofHom (S := K ⊗[O] Q) Algebra.TensorProduct.includeLeftRingHom) = _
   exact t.lift_fst _ _ _


-- created on 2026-10-05
