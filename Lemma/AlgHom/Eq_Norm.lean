import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped TensorProduct


attribute [local instance] Algebra.TensorProduct.rightAlgebra

private lemma repr_map
  {K L E F : Type*} [Field K] [Field L] [Algebra K L]
  [Field E] [Algebra K E] [Field F] [Algebra K F]
  {n : Type*} [Fintype n] [DecidableEq n]
  (b : Module.Basis n K L) (φ : E →ₐ[K] F) (y : E ⊗[K] L) (i : n) :
  (b.baseChange F).repr (Algebra.TensorProduct.map φ (AlgHom.id K L) y) i =
    φ ((b.baseChange E).repr y i) := by
  induction y using TensorProduct.inductionOn with
  | tmul e l =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Module.Basis.baseChange_repr_tmul, Module.Basis.baseChange_repr_tmul,
      Algebra.smul_def, Algebra.smul_def, map_mul, φ.commutes]
  | add y z hy hz =>
    simp only [map_add, Finsupp.add_apply, hy, hz]

private lemma comm_symm_map
  [Field K] [Field L] [Algebra K L]
  [Field E] [Algebra K E] [Field F] [Algebra K F]
  (ι : E →ₐ[K] F) (x : L ⊗[K] E) :
  (Algebra.TensorProduct.commRight K F L).symm
    (Algebra.TensorProduct.map (AlgHom.id K L) ι x) =
    Algebra.TensorProduct.map ι (AlgHom.id K L)
      ((Algebra.TensorProduct.commRight K E L).symm x) := by
  induction x using TensorProduct.inductionOn with
  | tmul l e =>
    simp [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.commRight_symm_tmul, AlgHom.id_apply]
  | add x₁ x₂ hx₁ hx₂ =>
    simp only [map_add, hx₁, hx₂]

/--
[Algebra_TensorProduct_map_norm_eq_norm_map_of_rightAlgebra](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_TensorProduct_map_norm_eq_norm_map_of_rightAlgebra.lean)
-/
@[path]
private lemma main
  [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [Field E] [Algebra K E] [Field F] [Algebra K F]
  {ι : E →ₐ[K] F}
  {x : L ⊗[K] E} :
-- imply
  ι (Algebra.norm E x) =
    Algebra.norm F (Algebra.TensorProduct.map (AlgHom.id K L) ι x) := by
-- proof
  classical
  let b := Module.finBasis K L
  let y : E ⊗[K] L := (Algebra.TensorProduct.commRight K E L).symm x
  have hnormE : Algebra.norm E x = Algebra.norm E y :=
    (Algebra.norm_eq_of_algEquiv (Algebra.TensorProduct.commRight K E L).symm x).symm
  let y' : F ⊗[K] L := Algebra.TensorProduct.map ι (AlgHom.id K L) y
  have hcomm : (Algebra.TensorProduct.commRight K F L).symm
    (Algebra.TensorProduct.map (AlgHom.id K L) ι x) = y' :=
    comm_symm_map ι x
  have hnormF : Algebra.norm F (Algebra.TensorProduct.map (AlgHom.id K L) ι x) =
      Algebra.norm F y' := by
    rw [← hcomm]
    apply (Algebra.norm_eq_of_algEquiv (Algebra.TensorProduct.commRight K F L).symm _).symm
  rw [hnormE, hnormF]
  rw [Algebra.norm_eq_matrix_det (b.baseChange E) y,
    Algebra.norm_eq_matrix_det (b.baseChange F) y', AlgHom.map_det]
  congr 1
  ext i j
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Module.Basis.baseChange_apply, Module.Basis.baseChange_apply]
  have hm : Algebra.TensorProduct.map ι (AlgHom.id K L) (y * (1 : E) ⊗ₜ[K] b j) =
      y' * (1 : F) ⊗ₜ[K] b j := by
    rw [map_mul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
  rw [← hm, repr_map]


-- created on 2026-10-20
