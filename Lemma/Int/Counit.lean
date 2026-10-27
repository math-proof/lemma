import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[Bialgebra_counit_comp_algEquiv_of_comul_compat](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Bialgebra_counit_comp_algEquiv_of_comul_compat.lean)
-/
@[path]
private lemma main
  [CommRing K]
  [CommRing B₁] [Bialgebra K B₁]
  [CommRing B₂] [Bialgebra K B₂]
  {φ : B₁ ≃ₐ[K] B₂}
  -- given
  (hφcomul : ∀ x, Coalgebra.comul (R := K) (φ x) = (_root_.TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := K) x)) :
  -- imply
  ∀ x, Coalgebra.counit (R := K) (φ x) = Coalgebra.counit (R := K) x := by
  -- proof
  intro x
  let η : B₁ →ₗ[K] K := (Coalgebra.counit (R := K) (A := B₂)).comp φ.toLinearMap
  have hηx : η x = Coalgebra.counit (R := K) (φ x) := rfl
  rw [← hηx]
  have key : ∀ y : B₁, (TensorProduct.lid K B₁) ((η.rTensor B₁) (Coalgebra.comul (R := K) y)) = y := by
    intro y
    apply φ.injective
    have hnat : ∀ z : K ⊗[K] B₁, φ ((TensorProduct.lid K B₁) z) = (TensorProduct.lid K B₂) (φ.toLinearMap.lTensor K z) := by
      intro z
      refine TensorProduct.inductionOn z ?_ ?_
      ·
        intro r b
        simp [TensorProduct.lid_tmul, map_smul]
      ·
        intro u v hu hv
        simp [map_add, hu, hv]
    rw [hnat]
    have hcomp2 : LinearMap.comp (φ.toLinearMap.lTensor K) (η.rTensor B₁) = LinearMap.comp ((Coalgebra.counit (R := K) (A := B₂)).rTensor B₂) (_root_.TensorProduct.map φ.toLinearMap φ.toLinearMap) := by
      ext a b
      simp [η, TensorProduct.map_tmul]
    rw [show φ.toLinearMap.lTensor K (η.rTensor B₁ (Coalgebra.comul y)) = (Coalgebra.counit (R := K) (A := B₂)).rTensor B₂ ((_root_.TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul y)) from congrFun (congrArg DFunLike.coe hcomp2) _]
    rw [← hφcomul y]
    have hax := Coalgebra.rTensor_counit_comp_comul (R := K) (A := B₂)
    have hax' := congrFun (congrArg DFunLike.coe hax) (φ y)
    simp only [LinearMap.comp_apply] at hax'
    rw [hax']
    simp [TensorProduct.lid_tmul]
  have hG_eq : Coalgebra.counit (R := K) ((TensorProduct.lid K B₁) ((η.rTensor B₁) (Coalgebra.comul (R := K) x))) = η x := by
    have hnat2 : ∀ z : K ⊗[K] B₁, Coalgebra.counit (R := K) ((TensorProduct.lid K B₁) z) = (TensorProduct.lid K K) ((Coalgebra.counit (R := K) (A := B₁)).lTensor K z) := by
      intro z
      refine TensorProduct.inductionOn z ?_ ?_
      ·
        intro r b
        simp [TensorProduct.lid_tmul, map_smul]
      ·
        intro u v hu hv
        simp [map_add, hu, hv]
    rw [hnat2]
    have hswap : LinearMap.comp ((Coalgebra.counit (R := K) (A := B₁)).lTensor K) (η.rTensor B₁) = LinearMap.comp (η.rTensor K) ((Coalgebra.counit (R := K) (A := B₁)).lTensor B₁) := by
      ext a b
      simp
    rw [show (Coalgebra.counit (R := K) (A := B₁)).lTensor K (η.rTensor B₁ (Coalgebra.comul x)) = η.rTensor K ((Coalgebra.counit (R := K) (A := B₁)).lTensor B₁ (Coalgebra.comul x)) from congrFun (congrArg DFunLike.coe hswap) _]
    have hax1 := Coalgebra.lTensor_counit_comp_comul (R := K) (A := B₁)
    have hax1' := congrFun (congrArg DFunLike.coe hax1) x
    simp only [LinearMap.comp_apply] at hax1'
    rw [hax1']
    simp [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
  rw [← hG_eq, key x]


-- created on 2026-10-20
