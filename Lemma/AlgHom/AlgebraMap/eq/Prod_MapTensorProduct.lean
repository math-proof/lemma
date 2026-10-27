import Mathlib
import Initialize.Tactic.Attr.Basic
open Matrix
open scoped TensorProduct


private noncomputable def galP
  [Field F] [Field M] [Algebra F M]
  {n : ℕ} (b : Module.Basis (Fin n) F M) (e : (M ≃ₐ[F] M) ≃ Fin n) :
  Matrix (Fin n) (Fin n) M :=
  fun i j => e.symm i (b j)

private lemma P_mul_A
  [Field F] [Field M] [Algebra F M]
  {n : ℕ} {b : Module.Basis (Fin n) F M} {e : (M ≃ₐ[F] M) ≃ Fin n}
  {x : M} :
-- imply
  galP b e * (Algebra.leftMulMatrix b x).map (algebraMap F M) =
    diagonal (fun i => e.symm i x) * galP b e := by
-- proof
  ext i k
  rw [Matrix.mul_apply, diagonal_mul]
  have hx : x * b k = ∑ j, (Algebra.leftMulMatrix b x) j k • b j := by
    conv_lhs => rw [← b.sum_repr (x * b k)]
    simp only [Algebra.leftMulMatrix_eq_repr_mul]
  have := congrArg (e.symm i) hx
  rw [map_mul, map_sum] at this
  simp only [Algebra.smul_def] at this
  rw [galP, this]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.map_apply, galP]
  rw [map_mul, AlgEquiv.commutes, mul_comm]

private lemma det_P_ne_zero
  [Field F] [Field M] [Algebra F M]
  {n : ℕ} {b : Module.Basis (Fin n) F M} {e : (M ≃ₐ[F] M) ≃ Fin n} :
-- imply
  (galP b e).det ≠ 0 := by
-- proof
  intro h0
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
  have hli : LinearIndependent M fun i : Fin n => ((e.symm i : M ≃ₐ[F] M) : M →ₐ[F] M).toLinearMap := by
    apply (linearIndependent_algHom_toLinearMap F M M).comp _
      (show Function.Injective (fun i : Fin n => ((e.symm i : M ≃ₐ[F] M) : M →ₐ[F] M)) by
        intro i j hij
        apply e.symm.injective
        apply AlgEquiv.ext
        intro x
        apply congrArg (fun φ : M →ₐ[F] M => φ x) hij)
  rw [Fintype.linearIndependent_iff] at hli
  apply hc0
  funext i
  refine hli c ?_ i
  apply b.ext
  intro k
  have hk := congrFun hc k
  simp only [vecMul, dotProduct, galP] at hk
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
    LinearMap.zero_apply, smul_eq_mul]
  simpa [AlgEquiv.coe_toAlgHom] using hk

private lemma leftMulMatrix_tmul
  [Field F] [Field M] [Algebra F M] [CommRing R] [Algebra F R]
  {n : ℕ} {b : Module.Basis (Fin n) F M}
  {bR : Module.Basis (Fin n) R (R ⊗[F] M)}
-- given
  (hbR : ∀ i, bR i = 1 ⊗ₜ[F] b i)
  {r : R}
  {x : M} :
-- imply
  Algebra.leftMulMatrix bR (r ⊗ₜ[F] x) = r • (Algebra.leftMulMatrix b x).map (algebraMap F R) := by
-- proof
  have hb : bR = Algebra.TensorProduct.basis R b := by
    apply Module.Basis.eq_of_apply_eq
    intro i
    rw [hbR, Algebra.TensorProduct.basis_apply]
  subst hb
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.TensorProduct.basis_repr_tmul]
  simp [Algebra.leftMulMatrix_eq_repr_mul]


/--
[Algebra_TensorProduct_algebraMap_norm_eq_prod_map_algEquiv](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_TensorProduct_algebraMap_norm_eq_prod_map_algEquiv.lean)
-/
@[path]
private lemma main
  [Field F] [Field M] [Algebra F M] [FiniteDimensional F M] [IsGalois F M]
  [CommRing R] [Algebra F R]
  {z : R ⊗[F] M} :
-- imply
  algebraMap R (R ⊗[F] M) (Algebra.norm R z) =
    ∏ g : M ≃ₐ[F] M, Algebra.TensorProduct.map (AlgHom.id F R) (g : M →ₐ[F] M) z := by
-- proof
  classical
  set n := Module.finrank F M
  let b : Module.Basis (Fin n) F M := Module.finBasis F M
  have hcard : Fintype.card (M ≃ₐ[F] M) = n := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  let e : (M ≃ₐ[F] M) ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let bR : Module.Basis (Fin n) R (R ⊗[F] M) := Algebra.TensorProduct.basis R b
  have hbR : ∀ i, bR i = 1 ⊗ₜ[F] b i := fun i => Algebra.TensorProduct.basis_apply b i
  let P : Matrix (Fin n) (Fin n) M := galP b e
  let ψM : M →ₐ[F] R ⊗[F] M := Algebra.TensorProduct.includeRight
  let ψR : R →+* R ⊗[F] M := algebraMap R (R ⊗[F] M)
  let act (g : M ≃ₐ[F] M) : R ⊗[F] M →ₐ[F] R ⊗[F] M :=
    Algebra.TensorProduct.map (AlgHom.id F R) (g : M →ₐ[F] M)
  have hP : P.map ψM * (Algebra.leftMulMatrix bR z).map ψR =
      diagonal (fun i => act (e.symm i) z) * P.map ψM := by
    have hmul : ∀ (r : R) (x : M),
        P.map ψM * (Algebra.leftMulMatrix bR (r ⊗ₜ[F] x)).map ψR =
          diagonal (fun i => act (e.symm i) (r ⊗ₜ[F] x)) * P.map ψM := by
      intro r x
      rw [leftMulMatrix_tmul hbR]
      have hmap : (r • (Algebra.leftMulMatrix b x).map (algebraMap F R)).map ψR =
        ψR r • ((Algebra.leftMulMatrix b x).map (algebraMap F M)).map ψM := by
        ext i j
        simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
        rw [AlgHom.commutes ψM, (IsScalarTower.algebraMap_apply F R (R ⊗[F] M) _).symm]
      rw [hmap, Matrix.mul_smul, ← Matrix.map_mul, P_mul_A (x := x) (b := b) (e := e),
        Matrix.map_mul, ← Matrix.smul_mul]
      congr 1
      ext i j
      simp only [Matrix.smul_apply, Matrix.map_apply, diagonal, of_apply, smul_eq_mul]
      split_ifs
      ·
        rw [show act (e.symm i) (r ⊗ₜ x) = r ⊗ₜ e.symm i x from rfl, show ψR r = r ⊗ₜ (1 : M) from rfl,
          show ψM (e.symm i x) = (1 : R) ⊗ₜ e.symm i x from rfl, Algebra.TensorProduct.tmul_mul_tmul,
          one_mul, mul_one]
      ·
        rw [map_zero, mul_zero]
    induction z using TensorProduct.inductionOn with
    | tmul r x =>
      apply hmul r x
    | add x y hx hy =>
      rw [map_add, Matrix.map_add, Matrix.mul_add, hx, hy, ← Matrix.add_mul]
      ·
        rw [diagonal_add]
        congr 1
        funext i
        simp
      ·
        intro a₁ a₂
        apply map_add
  have hdet := congrArg Matrix.det hP
  rw [det_mul, det_mul, det_diagonal] at hdet
  have hPunit : IsUnit (P.map ψM).det := by
    have : (P.map ψM).det = (ψM : M →+* R ⊗[F] M) P.det := by
      rw [RingHom.map_det]
      apply congrArg Matrix.det
      ext i j
      rfl
    rw [this]
    apply (isUnit_iff_ne_zero.mpr (det_P_ne_zero (b := b) (e := e))).map _
  have hL : (Algebra.leftMulMatrix bR z).det = Algebra.norm R z :=
    (Algebra.norm_eq_matrix_det bR z).symm
  have hLS : ((Algebra.leftMulMatrix bR z).map ψR).det = ψR (Algebra.norm R z) := by
    rw [← hL, RingHom.map_det]
    apply congrArg Matrix.det
    ext i j
    rfl
  rw [hLS, mul_comm] at hdet
  have hcancel := hPunit.mul_right_cancel hdet
  rw [hcancel, ← Equiv.prod_comp e.symm]


-- created on 2026-10-16
