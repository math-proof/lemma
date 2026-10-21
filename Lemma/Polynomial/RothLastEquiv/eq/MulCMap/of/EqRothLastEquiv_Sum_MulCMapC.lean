import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Nat.RothLastIndex.eq.AddRothSLastIndex.of.RothMvIndex
import Lemma.Polynomial.RothLastEquiv.eq.Sum_MulCMap.of.RothMvIndex.Eq_Sum_MulCMapC
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial
open Nat


private lemma lastIndex_add
  {n : ℕ}
  (i j : RothMvIndex n)
  (a b : ℕ) :
    rothLastIndex (i + j) (a + b) = rothLastIndex i a + rothLastIndex j b := by
  simpa [rothLastIndex] using
    RothLastIndex.eq.AddRothSLastIndex.of.RothMvIndex i j a b

/--
[rothHasseDet_lastEquiv_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {n k : ℕ}
  (P : MvPolynomial (Fin (n + 1)) ℚ)
  (phi : Fin k → MvPolynomial (Fin n) ℚ)
  (psi : Fin k → ℚ[X])
-- given
  (hP : rothLastEquiv ℚ n P =
    ∑ j, C (phi j) * map MvPolynomial.C (psi j))
  (i : Fin k → RothMvIndex n) :
-- imply
  rothLastEquiv ℚ n
    (rothHasseDet P
      (fun s ↦ rothLastIndex (i s) 0)
      (fun t ↦ rothLastIndex 0 t.val)) =
    C (Matrix.det fun s j ↦ rothMvHasse (i s) (phi j)) *
      map MvPolynomial.C
        (Matrix.det fun t j ↦ hasseDeriv t.val (psi j)) := by
-- proof
  classical
  let V : Matrix (Fin k) (Fin k) (MvPolynomial (Fin n) ℚ) :=
    fun s j ↦ rothMvHasse (i s) (phi j)
  let H : Matrix (Fin k) (Fin k) ℚ[X] :=
    fun t j ↦ hasseDeriv t.val (psi j)
  let B : Matrix (Fin k) (Fin k) (MvPolynomial (Fin (n + 1)) ℚ) :=
    fun s t ↦ rothMvHasse
      (rothLastIndex (i s) 0 + rothLastIndex 0 t.val) P
  let A : Matrix (Fin k) (Fin k) (Polynomial (MvPolynomial (Fin n) ℚ)) :=
    fun s t ↦ rothLastEquiv ℚ n
      (rothMvHasse (rothLastIndex (i s) t.val) P)
  let VC : Matrix (Fin k) (Fin k) (Polynomial (MvPolynomial (Fin n) ℚ)) :=
    fun s j ↦ C (V s j)
  let HC : Matrix (Fin k) (Fin k) (Polynomial (MvPolynomial (Fin n) ℚ)) :=
    fun j t ↦ map MvPolynomial.C (H t j)
  have hA : A = VC * HC := by
    funext s t
    rw [Matrix.mul_apply]
    dsimp [A, VC, HC, V, H]
    have h :=
      RothLastEquiv.eq.Sum_MulCMap.of.RothMvIndex.Eq_Sum_MulCMapC
        (rothLastEquiv ℚ n P) phi psi hP (i s) t.val
    simpa using h
  have hleft : rothLastEquiv ℚ n
    (rothHasseDet P
      (fun s ↦ rothLastIndex (i s) 0)
      (fun t ↦ rothLastIndex 0 t.val)) = A.det := by
    unfold rothHasseDet
    change rothLastEquiv ℚ n B.det = A.det
    calc
      _ = ((rothLastEquiv ℚ n).toRingHom.mapMatrix B).det :=
        RingHom.map_det (rothLastEquiv ℚ n).toRingHom B
      _ = A.det := by
        congr 1
        funext s t
        change rothLastEquiv ℚ n
          (rothMvHasse (rothLastIndex (i s) 0 + rothLastIndex 0 t.val) P) =
          rothLastEquiv ℚ n (rothMvHasse (rothLastIndex (i s) t.val) P)
        rw [← lastIndex_add]
        simp
  rw [hleft, hA, Matrix.det_mul]
  have hVC : VC.det = C V.det := by
    have hmatrix : VC = V.map C := by
      funext s j
      rfl
    rw [hmatrix]
    exact (RingHom.map_det
      (C : MvPolynomial (Fin n) ℚ →+* Polynomial (MvPolynomial (Fin n) ℚ)) V).symm
  have hHC : HC.det = map MvPolynomial.C H.det := by
    let f : ℚ[X] →+* Polynomial (MvPolynomial (Fin n) ℚ) :=
      mapRingHom MvPolynomial.C
    have hmatrix : HC = f.mapMatrix H.transpose := by
      ext j t
      rfl
    have hmapMatrix : f.mapMatrix H.transpose = H.transpose.map f := by
      rfl
    calc
      _ = (f.mapMatrix H.transpose).det := congrArg Matrix.det hmatrix
      _ = (H.transpose.map f).det := congrArg Matrix.det hmapMatrix
      _ = f H.transpose.det := (RingHom.map_det f H.transpose).symm
      _ = f H.det := by rw [Matrix.det_transpose]
      _ = map MvPolynomial.C H.det := rfl
  rw [hVC, hHC]


-- created on 2026-10-21
