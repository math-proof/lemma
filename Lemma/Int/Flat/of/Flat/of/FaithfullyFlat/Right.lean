import Mathlib
import sympy.Basic
open TensorProduct


private lemma of_flat_of_faithfullyFlat_right_aux
  (R S T : Type*) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]
  [Algebra R T] [IsScalarTower R S T] [Module.FaithfullyFlat S T] [Module.Flat R T] :
  Module.Flat R S := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ f hf
  rw [← LinearMap.baseChange_eq_ltensor, ← Module.FaithfullyFlat.lTensor_injective_iff_injective S T]
  have key : ∀ x,
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T P
      (((f.baseChange S).lTensor T) x) =
    f.lTensor T (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T N x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp [map_add, hx, hy]
    | tmul t y =>
      induction y using TensorProduct.inductionOn with
      | add a b ha hb => simp_all [tmul_add, map_add]
      | tmul s n => simp [LinearMap.lTensor_tmul, LinearMap.baseChange_tmul]
  have hT : Function.Injective (f.lTensor T) :=
    Module.Flat.lTensor_preserves_injective_linearMap f hf
  have hcomp :
    Function.Injective
      (Function.comp (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T P)
        ((f.baseChange S).lTensor T)) := by
    have hshow :
      Function.comp (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T P)
        ((f.baseChange S).lTensor T) =
      Function.comp (f.lTensor T)
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T N) :=
      funext key
    rw [hshow]
    exact hT.comp (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T N).injective
  exact hcomp.of_comp
/--
[Module_Flat_of_flat_of_faithfullyFlat_right](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_Flat_of_flat_of_faithfullyFlat_right.lean)
-/
@[path]
private lemma main
  [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T]
  [IsScalarTower R S T] [Module.FaithfullyFlat S T] [Module.Flat R T] :
-- imply
  Module.Flat R S :=
-- proof
  of_flat_of_faithfullyFlat_right_aux R S T


-- created on 2026-10-24
