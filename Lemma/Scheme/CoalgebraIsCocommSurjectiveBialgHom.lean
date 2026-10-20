import Mathlib
import sympy.Basic
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[Coalgebra_IsCocomm_of_surjective_bialgHom](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Coalgebra_IsCocomm_of_surjective_bialgHom.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommSemiring R]
  {A : Type u} [Semiring A] [Bialgebra R A] [Coalgebra.IsCocomm R A]
  {B : Type u} [Semiring B] [Bialgebra R B] (π : CoalgHom R A B) (hπ : Function.Surjective π) :
  -- imply
  Coalgebra.IsCocomm R B := by
  -- proof
  refine ⟨LinearMap.ext fun b => ?_⟩
  obtain ⟨a, rfl⟩ := hπ b
  have h0 := LinearMap.congr_fun (CoalgHomClass.map_comp_comul π) a
  simp only [LinearMap.comp_apply] at h0
  have hc : Coalgebra.comul (R := R) (π a) = TensorProduct.map π.toLinearMap π.toLinearMap (Coalgebra.comul (R := R) a) := h0.symm
  show TensorProduct.comm R B B (Coalgebra.comul (R := R) (π a)) = Coalgebra.comul (R := R) (π a)
  rw [hc]
  have hnat : ∀ w : A ⊗[R] A, TensorProduct.comm R B B (TensorProduct.map π.toLinearMap π.toLinearMap w) = TensorProduct.map π.toLinearMap π.toLinearMap (TensorProduct.comm R A A w) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul x y => simp
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy]
      rw [map_add (TensorProduct.comm R A A) x y, map_add]
  rw [hnat, Coalgebra.comm_comul]


-- created on 2026-10-20
