import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma matrixEquivTensor_symm_smul
  (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
  (n : Type) [Fintype n] [DecidableEq n]
  (a : A)
  (x : TensorProduct R A (Matrix n n R)) :
  -- imply
  (matrixEquivTensor n R A).symm (a • x) = a • (matrixEquivTensor n R A).symm x := by
  -- proof
  induction x using TensorProduct.inductionOn with
  | tmul b M =>
    rw [TensorProduct.smul_tmul', matrixEquivTensor_apply_symm, matrixEquivTensor_apply_symm, smul_eq_mul, mul_smul]
  | add x y hx hy =>
    rw [smul_add, map_add, map_add, hx, hy, smul_add]

private lemma linearIndependent_matrix_map
  (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
  (n : Type) [Fintype n] [DecidableEq n]
  {ι : Type}
  (M : ι → Matrix n n R)
  -- given
  (hM : LinearIndependent R M) :
  -- imply
  LinearIndependent A (fun i => (M i).map (algebraMap R A)) := by
  -- proof
  have h1 : LinearIndependent A (fun i => TensorProduct.tmul R (1 : A) (M i)) :=
    Module.Flat.linearIndependent_one_tmul hM
  have h2 := h1.map_of_injective_injective id (matrixEquivTensor n R A).symm.toAddEquiv.toAddMonoidHom
    (fun _ h => h) (fun x hx => by simpa using hx)
    (fun a x => by simpa using matrixEquivTensor_symm_smul R A n a x)
  convert h2 using 1
  ·
    funext i
    simp [matrixEquivTensor_apply_symm]

/--
[LinearIndependent_linearMap_baseChange_of_int](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LinearIndependent_linearMap_baseChange_of_int.lean)
-/
@[path]
private lemma main
  (K : Type) [Field K] [CharZero K]
  (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
  {ι : Type}
  (f : ι → Module.End ℤ Λ)
  -- given
  (hf : LinearIndependent ℤ f) :
  -- imply
  LinearIndependent K (fun i => ((f i).baseChange K : Module.End K (TensorProduct ℤ K Λ))) := by
  -- proof
  classical
  let b := Module.Free.chooseBasis ℤ Λ
  let bK := Algebra.TensorProduct.basis K b
  refine LinearIndependent.of_comp (LinearMap.toMatrix bK bK).toLinearMap ?_
  have key : ((LinearMap.toMatrix bK bK).toLinearMap ∘ fun i => ((f i).baseChange K : Module.End K (TensorProduct ℤ K Λ))) = fun i => (LinearMap.toMatrix b b (f i)).map (algebraMap ℤ K) := by
    funext i
    apply LinearMap.toMatrix_baseChange K (f i) b b
  rw [key]
  apply linearIndependent_matrix_map ℤ K _ (fun i => LinearMap.toMatrix b b (f i))
  · apply hf.map' (LinearMap.toMatrix b b).toLinearMap (LinearEquiv.ker _)


-- created on 2026-10-20
