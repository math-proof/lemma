import Mathlib
import sympy.Basic
open CategoryTheory AlgebraicGeometry IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma ringKrullDim_quotient_map_maximalIdeal_eq_zero
  (R S : Type*) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
  [IsLocalHom (algebraMap R S)] [Algebra.QuasiFinite R S] :
  ringKrullDim (S ⧸ (maximalIdeal R).map (algebraMap R S)) = 0 := by
  let e : (maximalIdeal R).Fiber S ≃ₐ[R] S ⧸ (maximalIdeal R).map (algebraMap R S) :=
    (Algebra.TensorProduct.congr (.symm <| .ofBijective _
      (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))) .refl).trans <|
    (Algebra.TensorProduct.comm _ _ _).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (maximalIdeal R)).symm.restrictScalars R)
  let _ : IsArtinianRing ((maximalIdeal R).Fiber S) := inferInstance
  let hA : IsArtinianRing (S ⧸ (maximalIdeal R).map (algebraMap R S)) := e.surjective.isArtinianRing
  let _ : Ring.KrullDimLE 0 (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
    (isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mp hA).2
  let _ : Nontrivial (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by
    rw [Ideal.Quotient.nontrivial_iff]
    exact ((((local_hom_TFAE (algebraMap R S)).out 1 3 rfl rfl).mp inferInstance).trans_lt
      (inferInstance : (maximalIdeal S).IsMaximal).ne_top.lt_top).ne
  apply ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance
/--
[AlgebraicGeometry_LocallyQuasiFinite_ringKrullDim_stalk_quotient_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_LocallyQuasiFinite_ringKrullDim_stalk_quotient_eq_zero.lean)
-/
@[path]
private lemma main
  {X Y : Scheme} (g : X ⟶ Y) [LocallyQuasiFinite g] (x : X) :
  ringKrullDim ((X.presheaf.stalk x) ⧸ (maximalIdeal (Y.presheaf.stalk (g.base x))).map (g.stalkMap x).hom) = 0 := by
  let _ : Algebra (Y.presheaf.stalk (g.base x)) (X.presheaf.stalk x) := (g.stalkMap x).hom.toAlgebra
  let _ : Algebra.QuasiFinite (Y.presheaf.stalk (g.base x)) (X.presheaf.stalk x) := g.quasiFiniteAt x
  let _ : IsLocalHom (algebraMap (Y.presheaf.stalk (g.base x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (g.stalkMap x).hom)
  apply ringKrullDim_quotient_map_maximalIdeal_eq_zero (Y.presheaf.stalk (g.base x)) (X.presheaf.stalk x)


-- created on 2026-10-20
