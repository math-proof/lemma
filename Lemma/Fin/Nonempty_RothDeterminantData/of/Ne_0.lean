import Mathlib
import Lemma.Fin.RothMvL1_RothMvHasse.le.MulPow2SumRothMvL1.of.RothMvIndex
import Lemma.Fin.RothMvL1Det.le.MulFactorialPow.of.All_LeRothMvL1
import Lemma.Fin.RothDegreeBoundOver_RothMvHasse.of.RothMvIndex
import Lemma.Fin.RothDegreeBound.of.All_RothDegreeBound
import Lemma.Fin.MapRothMvHasse.eq.RothMvHasse_Map.of.RothMvIndex
import Lemma.Fin.Any_And_Det_RothMvHasse.ne.Zero.of.All_RothDegreeBoundOver.LinearIndependent
import Lemma.Fin.LeNatDegreeRothLastEquiv
import Lemma.Fin.MapRothHasseDet.eq.RothHasseDet_Map
import Lemma.Fin.RothDegreeBoundOver
import Lemma.Fin.RothDegreeBoundOver_Map
import Lemma.Fin.RothDegreeBound_RothHasseDetMul
import Lemma.Fin.RothLastEquiv_Map.eq.Map_MapRothLastEquiv
import Lemma.Fin.RothMvL1_CoeffRothLastEquiv.le.RothMvL1
import Lemma.Fin.RothMvL1_RothHasseDet.le.MulFactorialPowMulPow2SumRothMvL1
import Lemma.Polynomial.Any_And_Le_AddNatDegree1AndAll_Eq_CoeffAndAll_LeNatDegreeAndLinearIndependentAndLinearIndependentAndEq_Sum_MulCMap.of.Ne_0
import Lemma.Polynomial.Det_HasseDerivVal.ne.Zero.of.LinearIndependent
import Lemma.Nat.RothLastIndex.eq.AddRothSLastIndex.of.RothMvIndex
import Lemma.Polynomial.RothLastEquiv.eq.Sum_MulCMap.of.RothMvIndex.Eq_Sum_MulCMapC
open MathlibExt.NumberTheory.RothAuxiliary
open Fin
open Polynomial
open Nat
set_option maxHeartbeats 800000


private lemma lastIndex_add
  {n : ℕ}
  (i j : RothMvIndex n)
  (a b : ℕ) :
    rothLastIndex (i + j) (a + b) = rothLastIndex i a + rothLastIndex j b := by
  simpa [rothLastIndex] using
    RothLastIndex.eq.AddRothSLastIndex.of.RothMvIndex i j a b

private lemma hasseDet_lastEquiv_factorization
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

/--
[roth_exists_determinant_data](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  (P : MvPolynomial (Fin (n + 1)) ℤ) (r : Fin (n + 1) → ℕ)
-- given
  (hPne : P ≠ 0)
  (hPdeg : rothDegreeBound P r) :
-- imply
  Nonempty (RothDeterminantData P r) := by
-- proof
  classical
  let castQ : ℤ →+* ℚ := algebraMap ℤ ℚ
  let PQ := MvPolynomial.map castQ P
  let Q := rothLastEquiv ℚ n PQ
  have hPQne : PQ ≠ 0 := by
    simpa [PQ] using (MvPolynomial.map_injective castQ Int.cast_injective).ne hPne
  have hQne : Q ≠ 0 := (rothLastEquiv ℚ n).injective.ne hPQne
  obtain ⟨k, phi, psi, hk, hkQ, hphi, hpsiDeg, hphiLI, hpsiLI, hdecomp⟩ :=
    Any_And_Le_AddNatDegree1AndAll_Eq_CoeffAndAll_LeNatDegreeAndLinearIndependentAndLinearIndependentAndEq_Sum_MulCMap.of.Ne_0
      Q hQne
  have hPQdeg : rothDegreeBoundOver PQ r :=
    RothDegreeBoundOver_Map castQ hPdeg
  have hQdeg : Q.natDegree ≤ r (Fin.last n) :=
    LeNatDegreeRothLastEquiv hPQdeg
  have hkR : k ≤ r (Fin.last n) + 1 := hkQ.trans (Nat.add_le_add_right hQdeg 1)
  choose a haQ hphiCoeff using hphi
  let phiZ : Fin k → MvPolynomial (Fin n) ℤ :=
    fun j ↦ (rothLastEquiv ℤ n P).coeff (a j)
  have hphiMap : ∀ j, MvPolynomial.map castQ (phiZ j) = phi j := by
    intro j
    have hmap := congrArg (fun F : Polynomial (MvPolynomial (Fin n) ℚ) ↦
      F.coeff (a j)) (RothLastEquiv_Map.eq.Map_MapRothLastEquiv castQ P)
    rw [Polynomial.coeff_map] at hmap
    exact hmap.symm.trans (hphiCoeff j).symm
  have hphiZdeg : ∀ j, rothDegreeBound (phiZ j) (fun h ↦ r h.castSucc) := by
    intro j
    exact RothDegreeBoundOver (show rothDegreeBoundOver P r from hPdeg) (a j)
  have hphiDeg : ∀ j, rothDegreeBoundOver (phi j) (fun h ↦ r h.castSucc) := by
    intro j
    rw [← hphiMap j]
    exact RothDegreeBoundOver_Map castQ (hphiZdeg j)
  obtain ⟨row, hrowOrder, hrowDet⟩ :=
    Any_And_Det_RothMvHasse.ne.Zero.of.All_RothDegreeBoundOver.LinearIndependent
      phi (fun h ↦ r h.castSucc) hphiLI hphiDeg
  let V : MvPolynomial (Fin n) ℤ :=
    Matrix.det fun s j ↦ rothMvHasse (row s) (phiZ j)
  let W : ℚ[X] := Matrix.det fun t j ↦ Polynomial.hasseDeriv t.val (psi j)
  let U : MvPolynomial (Fin (n + 1)) ℤ := rothHasseDet P
    (fun s ↦ rothLastIndex (row s) 0)
    (fun t ↦ rothLastIndex 0 t.val)
  have hVmap : MvPolynomial.map castQ V =
    Matrix.det fun s j ↦ rothMvHasse (row s) (phi j) := by
    let A : Matrix (Fin k) (Fin k) (MvPolynomial (Fin n) ℤ) :=
      fun s j ↦ rothMvHasse (row s) (phiZ j)
    change MvPolynomial.map castQ A.det = _
    rw [RingHom.map_det]
    congr 1
    funext s j
    change MvPolynomial.map castQ (rothMvHasse (row s) (phiZ j)) = _
    rw [MapRothMvHasse.eq.RothMvHasse_Map.of.RothMvIndex, hphiMap]
  exact ⟨{
    k := k
    k_pos := hk
    k_le := hkR
    row := row
    row_order := hrowOrder
    V := V
    W := W
    U := U
    V_ne := by
      intro hzero
      apply hrowDet
      rw [← hVmap, hzero, map_zero]
    W_ne := Det_HasseDerivVal.ne.Zero.of.LinearIndependent psi hpsiLI
    U_def := rfl
    factorization := by
      have hUmap : MvPolynomial.map castQ U = rothHasseDet PQ
        (fun s ↦ rothLastIndex (row s) 0)
        (fun t ↦ rothLastIndex 0 t.val) := by
        dsimp [U, PQ]
        exact MapRothHasseDet.eq.RothHasseDet_Map castQ P _ _
      rw [hUmap, hVmap]
      exact hasseDet_lastEquiv_factorization PQ phi psi hdecomp row
    V_degree := by
      dsimp [V]
      apply RothDegreeBound.of.All_RothDegreeBound
      intro s j
      exact RothDegreeBoundOver_RothMvHasse.of.RothMvIndex (hphiZdeg j) (row s)
    U_degree := by
      dsimp [U]
      exact RothDegreeBound_RothHasseDetMul hPdeg _ _
    V_l1 := by
      dsimp [V]
      apply RothMvL1Det.le.MulFactorialPow.of.All_LeRothMvL1
      intro s j
      calc
        _ ≤ 2 ^ (∑ h : Fin n, r h.castSucc) * rothMvL1 (phiZ j) :=
          RothMvL1_RothMvHasse.le.MulPow2SumRothMvL1.of.RothMvIndex
            (phiZ j) (row s) _ (hphiZdeg j)
        _ ≤ 2 ^ (∑ h : Fin n, r h.castSucc) * rothMvL1 P := by
          gcongr
          exact RothMvL1_CoeffRothLastEquiv.le.RothMvL1 P (a j)
    U_l1 := by
      dsimp [U]
      exact RothMvL1_RothHasseDet.le.MulFactorialPowMulPow2SumRothMvL1 P r hPdeg _ _
  }⟩


-- created on 2026-10-21
