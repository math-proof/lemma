import Mathlib
import sympy.Basic
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

variable {R : Type u} [CommRing R] (R' : Type w) [CommRing R'] [Algebra R R']
variable {H : Type v} [CommRing H] [HopfAlgebra R H]

private noncomputable abbrev bc (u : H →ₐ[R] H) : R' ⊗[R] H →ₐ[R'] R' ⊗[R] H :=
  Algebra.TensorProduct.map (AlgHom.id R' R') u

private lemma convMul_bc_tmul
  (u v : WithConv (H →ₐ[R] H))
  (s : R')
  (h : H) :
  -- imply
  (WithConv.toConv (bc R' u.ofConv) * WithConv.toConv (bc R' v.ofConv)).ofConv (s ⊗ₜ[R] h) = s ⊗ₜ[R] (u * v).ofConv h := by
  -- proof
  classical
  rw [AlgHom.convMul_apply, AlgHom.convMul_apply, TensorProduct.comul_tmul]
  let ρ := Coalgebra.Repr.arbitrary R h
  rw [← ρ.eq]
  change (Algebra.TensorProduct.lift (bc R' u.ofConv) (bc R' v.ofConv) _) ((TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R' R R' R' R' H H) ((1 ⊗ₜ[R'] s) ⊗ₜ[R] ∑ i ∈ ρ.index, ρ.left i ⊗ₜ[R] ρ.right i)) = s ⊗ₜ[R] (Algebra.TensorProduct.lift u.ofConv v.ofConv _) (∑ i ∈ ρ.index, ρ.left i ⊗ₜ[R] ρ.right i)
  rw [TensorProduct.tmul_sum, map_sum, map_sum, map_sum, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
  simp [bc, Algebra.TensorProduct.tmul_mul_tmul]

private lemma convMul_bc
  (u v : WithConv (H →ₐ[R] H)) :
  -- imply
  WithConv.toConv (bc R' u.ofConv) * WithConv.toConv (bc R' v.ofConv) = WithConv.toConv (bc R' (u * v).ofConv) := by
  -- proof
  apply WithConv.ext
  apply AlgHom.toLinearMap_injective
  apply TensorProduct.AlgebraTensorModule.ext
  intro s h
  change (WithConv.toConv (bc R' u.ofConv) * WithConv.toConv (bc R' v.ofConv)).ofConv (s ⊗ₜ[R] h) = (bc R' (u * v).ofConv) (s ⊗ₜ[R] h)
  rw [convMul_bc_tmul]
  simp [bc]

private lemma convOne_bc :
  -- imply
  (1 : WithConv (R' ⊗[R] H →ₐ[R'] R' ⊗[R] H)) = WithConv.toConv (bc R' (1 : WithConv (H →ₐ[R] H)).ofConv) := by
  -- proof
  apply WithConv.ext
  apply AlgHom.toLinearMap_injective
  apply TensorProduct.AlgebraTensorModule.ext
  intro s h
  rw [AlgHom.convOne_def, AlgHom.convOne_def]
  change algebraMap R' (R' ⊗[R] H) (Coalgebra.counit (s ⊗ₜ[R] h)) = s ⊗ₜ[R] algebraMap R H (Coalgebra.counit h)
  rw [TensorProduct.counit_tmul]
  change algebraMap R' (R' ⊗[R] H) (Coalgebra.counit (R := R) h • s) = _
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

private lemma pow_bc
  (u : WithConv (H →ₐ[R] H))
  (k : ℕ) :
  -- imply
  (WithConv.toConv (bc R' u.ofConv)) ^ k = WithConv.toConv (bc R' (u ^ k).ofConv) := by
  -- proof
  induction k
  · rw [pow_zero, pow_zero, convOne_bc]
  ·
    rename_i k ih
    rw [pow_succ, pow_succ, ih, convMul_bc]

/--
[HopfAlgebra_toConv_id_pow_eq_one_baseChange](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HopfAlgebra_toConv_id_pow_eq_one_baseChange.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  (R' : Type w) [CommRing R'] [Algebra R R']
  {H : Type v} [CommRing H] [HopfAlgebra R H]
  (m : ℕ)
  -- given
  (h : (WithConv.toConv (AlgHom.id R H)) ^ m = 1) :
  -- imply
  (WithConv.toConv (AlgHom.id R' (TensorProduct R R' H))) ^ m = 1 := by
  -- proof
  have hid : AlgHom.id R' (R' ⊗[R] H) = bc R' (WithConv.toConv (AlgHom.id R H)).ofConv := by
    change AlgHom.id R' (R' ⊗[R] H) = Algebra.TensorProduct.map (AlgHom.id R' R') (AlgHom.id R H)
    apply Algebra.TensorProduct.map_id.symm
  rw [hid]
  change (WithConv.toConv (bc R' (WithConv.toConv (AlgHom.id R H)).ofConv)) ^ m = 1
  rw [pow_bc, h, ← convOne_bc]


-- created on 2026-10-20
