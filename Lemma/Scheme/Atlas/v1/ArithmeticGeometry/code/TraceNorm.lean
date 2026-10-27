import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.TraceNorm
open IntermediateField Polynomial Module in


/--
[Matrix.charpoly_blockDiagonal_const](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TraceNorm.lean)
-/
@[path]
lemma Matrix.charpoly_blockDiagonal_const
  {K : Type*}
  {L : Type*}
  [CommRing K]
  [CommRing L]
  [Algebra K L]
  [CommRing R]
  [DecidableEq n]
  [Fintype n]
  [DecidableEq m]
  [Fintype m]
  {M : Matrix n n R} :
-- imply
  (Matrix.blockDiagonal (fun _ : m => M)).charpoly = M.charpoly ^ Fintype.card m := by
-- proof
  simp only [Matrix.charpoly]
  suffices h : Matrix.charmatrix (Matrix.blockDiagonal (fun _ : m => M)) =
    Matrix.blockDiagonal (fun _ : m => Matrix.charmatrix M) by
    rw [h, Matrix.det_blockDiagonal, Finset.prod_const, Finset.card_univ]
  ext ⟨i, k⟩ ⟨j, k'⟩
  simp only [Matrix.charmatrix, Matrix.blockDiagonal, Matrix.of_apply, Matrix.sub_apply,
    Matrix.scalar_apply, Matrix.diagonal_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all
set_option maxHeartbeats 400000 in

/--
[charpoly_lmul_eq_minpoly_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TraceNorm.lean)
-/
@[path]
lemma charpoly_lmul_eq_minpoly_pow
  {K : Type*}
  {L : Type*}
  [CommRing K]
  [CommRing L]
  [Algebra K L]
  [Field K]
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  {α : L}
-- given
  (hα_int : IsIntegral K α) :
-- imply
  (Algebra.lmul K L α).charpoly = (minpoly K α) ^ (finrank K L / finrank K K⟮α⟯) := by
-- proof
  let pb := adjoin.powerBasis hα_int
  haveI : FiniteDimensional (↥K⟮α⟯) L := finiteDimensional_right K⟮α⟯
  haveI : FiniteDimensional K (↥K⟮α⟯) := pb.finite
  let bKL := Module.finBasis (↥K⟮α⟯) L
  have hα_eq : α = algebraMap (↥K⟮α⟯) L (AdjoinSimple.gen K α) := by simp
  have h_mat : (LinearMap.toMatrix (pb.basis.smulTower bKL) (pb.basis.smulTower bKL)
    (LinearMap.mulLeft K α)) =
    Matrix.blockDiagonal
      (fun _ => Algebra.leftMulMatrix pb.basis (AdjoinSimple.gen K α)) := by
    rw [Algebra.toMatrix_lmul_eq]
    show Algebra.leftMulMatrix (pb.basis.smulTower bKL) α = _
    calc Algebra.leftMulMatrix (pb.basis.smulTower bKL) α
      = Algebra.leftMulMatrix (pb.basis.smulTower bKL)
        (algebraMap (↥K⟮α⟯) L (AdjoinSimple.gen K α)) := by rw [← hα_eq]
      _ = _ := Algebra.smulTower_leftMulMatrix_algebraMap pb.basis bKL _
  have h_charpoly : (Algebra.lmul K L α).charpoly =
    (Matrix.blockDiagonal (fun _ : Fin (finrank (↥K⟮α⟯) L) =>
      Algebra.leftMulMatrix pb.basis (AdjoinSimple.gen K α))).charpoly := by
    change (LinearMap.mulLeft K α).charpoly = _
    rw [← LinearMap.charpoly_toMatrix (LinearMap.mulLeft K α) (pb.basis.smulTower bKL), h_mat]
  rw [h_charpoly, Matrix.charpoly_blockDiagonal_const, Fintype.card_fin]
  have h_minpoly : (Algebra.leftMulMatrix pb.basis (AdjoinSimple.gen K α)).charpoly =
    minpoly K α := by
    rw [show AdjoinSimple.gen K α = pb.gen from (adjoin.powerBasis_gen hα_int).symm,
      charpoly_leftMulMatrix]
    exact minpoly_gen K α
  rw [h_minpoly]
  congr 1
  exact (Nat.div_eq_of_eq_mul_right finrank_pos
    (finrank_mul_finrank K (↥K⟮α⟯) L).symm).symm


-- created on 2026-10-23
