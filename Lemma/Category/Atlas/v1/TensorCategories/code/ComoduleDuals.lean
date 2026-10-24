import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.ComoduleDuals
open Coalgebra HopfAlgebra LinearMap
open scoped TensorProduct


/--
[lid_contractLeft_rTensor_assoc_eq_lid_rTensor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ComoduleDuals.lean)
-/
@[path]
lemma lid_contractLeft_rTensor_assoc_eq_lid_rTensor
  {k : Type u}
  [CommSemiring k]
  {H : Type v}
  [Semiring H]
  [HopfAlgebra k H]
  {X : Type v}
  [AddCommGroup X]
  [Module k X]
  [Module.Free k X]
  [Module.Finite k X]
  {f : Module.Dual k X} :
-- imply
  (TensorProduct.lid k H).toLinearMap ∘ₗ (contractLeft k X).rTensor H ∘ₗ (TensorProduct.assoc k (Module.Dual k X) X H).symm.toLinearMap ∘ₗ (TensorProduct.mk k (Module.Dual k X) (X ⊗[k] H)) f = (TensorProduct.lid k H).toLinearMap ∘ₗ f.rTensor H := by
-- proof
  ext y h
  simp [contractLeft, rTensor_tmul, TensorProduct.assoc_symm_tmul,
    TensorProduct.mk_apply, TensorProduct.lid_tmul]

/--
[dualTensorHom_lTensor_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ComoduleDuals.lean)
-/
@[path]
lemma dualTensorHom_lTensor_comp
  {k : Type u}
  [CommSemiring k]
  {H : Type v}
  [Semiring H]
  [HopfAlgebra k H]
  {X : Type v}
  [AddCommGroup X]
  [Module k X]
  [Module.Free k X]
  [Module.Finite k X]
  [AddCommMonoid N]
  [Module k N]
  [AddCommMonoid P]
  [Module k P]
  {g : N →ₗ[k] P}
  {t : Module.Dual k X ⊗[k] N}
  {m : X} :
-- imply
  (dualTensorHom k X P (g.lTensor (Module.Dual k X) t)) m = g ((dualTensorHom k X N t) m) := by
-- proof
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul f n =>
    simp [dualTensorHom_apply, LinearMap.lTensor_tmul, map_smul]
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply]; rw [hx, hy]

/--
[counit_comp_dualCoactCurried](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ComoduleDuals.lean)
-/
@[path]
lemma counit_comp_dualCoactCurried
  {k : Type u}
  [CommSemiring k]
  {H : Type v}
  [Semiring H]
  [HopfAlgebra k H]
  {X : Type v}
  [AddCommGroup X]
  [Module k X]
  [Module.Free k X]
  [Module.Finite k X]
  {π : X →ₗ[k] X ⊗[k] H}
  {f : Module.Dual k X}
-- given
  (hcounit : Coalgebra.counit.lTensor X ∘ₗ π = (TensorProduct.mk k X k).flip 1) :
-- imply
  Coalgebra.counit ∘ₗ dualCoactCurried k H X π f = f := by
-- proof
  ext m
  simp only [coe_comp, Function.comp_apply]
  show Coalgebra.counit (dualCoactUncurried k H X π (f ⊗ₜ[k] m)) = f m
  unfold dualCoactUncurried
  simp only [coe_comp, Function.comp_apply, LinearEquiv.coe_coe, lTensor_tmul]
  have hs1 := congr_fun (congr_arg DFunLike.coe
    (lid_contractLeft_rTensor_assoc_eq_lid_rTensor k H X f))
    ((HopfAlgebra.antipode k : H →ₗ[k] H).lTensor X (π m))
  simp only [coe_comp, Function.comp_apply, LinearEquiv.coe_coe, TensorProduct.mk_apply] at hs1
  rw [hs1]
  have hs2 : Coalgebra.counit ∘ₗ (TensorProduct.lid k H).toLinearMap ∘ₗ f.rTensor H =
    (TensorProduct.lid k k).toLinearMap ∘ₗ f.rTensor k ∘ₗ
      (Coalgebra.counit (R := k)).lTensor X := by
    ext y h; simp [rTensor_tmul, TensorProduct.lid_tmul, map_smul]
  have hs2' := congr_fun (congr_arg DFunLike.coe hs2)
    ((HopfAlgebra.antipode k : H →ₗ[k] H).lTensor X (π m))
  simp only [coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at hs2'
  rw [hs2']
  have hs3 : (Coalgebra.counit (R := k)).lTensor X
    ((HopfAlgebra.antipode k : H →ₗ[k] H).lTensor X (π m)) =
    (Coalgebra.counit (R := k)).lTensor X (π m) := by
    have : (Coalgebra.counit (R := k)).lTensor X ∘ₗ
      (HopfAlgebra.antipode k : H →ₗ[k] H).lTensor X =
      (Coalgebra.counit (R := k)).lTensor X := by
      ext y h; simp [lTensor_tmul, counit_antipode]
    exact congr_fun (congr_arg DFunLike.coe this) (π m)
  rw [hs3]
  have hs4 : (Coalgebra.counit (R := k)).lTensor X (π m) = m ⊗ₜ[k] (1 : k) :=
    congr_fun (congr_arg DFunLike.coe hcounit) m
  rw [hs4]
  simp [TensorProduct.lid_tmul]

/--
[dualCoaction_counit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ComoduleDuals.lean)
-/
@[path]
lemma dualCoaction_counit
  {k : Type u}
  [CommSemiring k]
  {H : Type v}
  [Semiring H]
  [HopfAlgebra k H]
  {X : Type v}
  [AddCommGroup X]
  [Module k X]
  [Module.Free k X]
  [Module.Finite k X]
-- given
  (hπ : RightComodule k H X) :
-- imply
  Coalgebra.counit.lTensor (Module.Dual k X) ∘ₗ (dualCoaction k H X hπ.coact) = (TensorProduct.mk k (Module.Dual k X) k).flip 1 := by
-- proof
  ext f
  apply (dualTensorHomEquiv k X k).injective
  ext m
  simp only [coe_comp, Function.comp_apply,
    dualTensorHomEquiv, dualTensorHomEquivOfBasis_apply]
  rw [dualTensorHom_lTensor_comp k X (Coalgebra.counit (R := k)) (dualCoaction k H X hπ.coact f) m]
  show Coalgebra.counit ((dualTensorHom k X H (dualCoaction k H X hπ.coact f)) m) =
    (dualTensorHom k X k (((TensorProduct.mk k (Module.Dual k X) k).flip 1) f)) m
  have lhs_eq : (dualTensorHom k X H (dualCoaction k H X hπ.coact f)) m =
    dualCoactCurried k H X hπ.coact f m := by
    unfold dualCoaction
    simp only [coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    rw [show (dualTensorHom k X H
      ((dualTensorHomEquiv k X H).symm (dualCoactCurried k H X hπ.coact f))) m =
      (dualTensorHomEquiv k X H
      ((dualTensorHomEquiv k X H).symm (dualCoactCurried k H X hπ.coact f))) m from rfl]
    simp [LinearEquiv.apply_symm_apply]
  rw [lhs_eq]
  have := congr_fun (congr_arg DFunLike.coe
    (counit_comp_dualCoactCurried k H X hπ.coact hπ.counit_coact f)) m
  simp only [coe_comp, Function.comp_apply] at this
  rw [this]
  simp [dualTensorHom_apply, LinearMap.flip_apply, TensorProduct.mk_apply]
/-- Remark 1.22.7 / Corollary 1.22.6: The linear dual of a finite-dimensional right
`H`-comodule carries a natural right `H`-comodule structure via the antipode. -/
@[reducible]


-- created on 2026-10-23
