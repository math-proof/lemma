import Mathlib
import Lemma.ModularCurve.ProjectiveLine
import Instance.ProjectiveLineMatrixAction
import Abbrev.ProjectiveLineMatrixAction

namespace ModularCurve.ProjectiveLine

variable {R : Type*} [CommRing R]

def vecMulRow (M : Matrix (Fin 2) (Fin 2) R) (hM : IsUnit M.det) (v : UnimodularRow R) :
    UnimodularRow R :=
  ⟨(v.1.1 * M 0 0 + v.1.2 * M 1 0, v.1.1 * M 0 1 + v.1.2 * M 1 1), by
    obtain ⟨x, y, h⟩ := v.2
    obtain ⟨e, he⟩ := hM.exists_left_inv
    rw [Matrix.det_fin_two] at he
    exact ⟨e * (x * M 1 1 - y * M 0 1), e * (y * M 0 0 - x * M 1 0), by
      linear_combination (x * v.1.1 + y * v.1.2) * he + h⟩⟩

@[simp]
theorem vecMulRow_fst (M : Matrix (Fin 2) (Fin 2) R) (hM : IsUnit M.det) (v : UnimodularRow R) :
    (vecMulRow M hM v).1.1 = v.1.1 * M 0 0 + v.1.2 * M 1 0 :=
  rfl

@[simp]
theorem vecMulRow_snd (M : Matrix (Fin 2) (Fin 2) R) (hM : IsUnit M.det) (v : UnimodularRow R) :
    (vecMulRow M hM v).1.2 = v.1.1 * M 0 1 + v.1.2 * M 1 1 :=
  rfl

def vecMul (M : Matrix (Fin 2) (Fin 2) R) (hM : IsUnit M.det) : ProjectiveLine R → ProjectiveLine R :=
  Quotient.map (vecMulRow M hM) <| by
    rintro v w ⟨u, h1, h2⟩
    refine ⟨u, ?_, ?_⟩
    · simp only [vecMulRow_fst]
      linear_combination M 0 0 * h1 + M 1 0 * h2
    · simp only [vecMulRow_snd]
      linear_combination M 0 1 * h1 + M 1 1 * h2

@[simp]
theorem vecMul_mk (M : Matrix (Fin 2) (Fin 2) R) (hM : IsUnit M.det) (v : UnimodularRow R) :
    vecMul M hM (⟦v⟧ : ProjectiveLine R) = ⟦vecMulRow M hM v⟧ :=
  rfl

theorem vecMul_one (h : IsUnit (1 : Matrix (Fin 2) (Fin 2) R).det) (P : ProjectiveLine R) :
    vecMul 1 h P = P := by
  induction P using Quotient.inductionOn with
  | h v =>
    rw [vecMul_mk]
    congr 1
    apply Subtype.ext
    refine Prod.ext ?_ ?_ <;> simp

theorem vecMul_mul (M M' : Matrix (Fin 2) (Fin 2) R) (hM : IsUnit M.det) (hM' : IsUnit M'.det)
    (hMM' : IsUnit (M * M').det) (P : ProjectiveLine R) :
    vecMul (M * M') hMM' P = vecMul M' hM' (vecMul M hM P) := by
  induction P using Quotient.inductionOn with
  | h v =>
    simp only [vecMul_mk]
    congr 1
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · simp only [vecMulRow_fst, vecMulRow_snd, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    · simp only [vecMulRow_fst, vecMulRow_snd, Matrix.mul_apply, Fin.sum_univ_two]
      ring

end ModularCurve.ProjectiveLine

namespace HeckeEis

open ModularCurve
open scoped MatrixGroups

noncomputable def projLineAct (N : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ) :
    ProjectiveLine (ZMod N) → ProjectiveLine (ZMod N) :=
  open scoped Classical in
  if h : IsUnit (redMat N M).det then ProjectiveLine.vecMul (redMat N M) h else id

theorem projLineAct_of_isUnit (N : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ) (h : IsUnit (redMat N M).det) :
    projLineAct N M = ProjectiveLine.vecMul (redMat N M) h := by
  classical
  rw [projLineAct, dif_pos h]

theorem isUnit_det_redMat_coe (N : ℕ) (g : SL(2, ℤ)) : IsUnit (redMat N (g : Matrix (Fin 2) (Fin 2) ℤ)).det := by
  have : (redMat N (g : Matrix (Fin 2) (Fin 2) ℤ)).det = 1 := by
    rw [redMat, ← RingHom.mapMatrix_apply, ← RingHom.map_det, g.det_coe, map_one]
  rw [this]
  exact isUnit_one

@[simp]
theorem projLineAct_one (N : ℕ) (P : ProjectiveLine (ZMod N)) : projLineAct N 1 P = P := by
  have h1 : redMat N 1 = 1 := by simp [redMat]
  have h : IsUnit (redMat N (1 : Matrix (Fin 2) (Fin 2) ℤ)).det := by rw [h1, Matrix.det_one]; exact isUnit_one
  rw [projLineAct_of_isUnit N 1 h]
  have h' : IsUnit (1 : Matrix (Fin 2) (Fin 2) (ZMod N)).det := by rw [Matrix.det_one]; exact isUnit_one
  rw [show ProjectiveLine.vecMul (redMat N 1) h = ProjectiveLine.vecMul 1 h' from by congr 1]
  exact ProjectiveLine.vecMul_one h' P

theorem projLineAct_mul (N : ℕ) (M M' : Matrix (Fin 2) (Fin 2) ℤ)
    (hM : IsUnit (redMat N M).det) (hM' : IsUnit (redMat N M').det) (P : ProjectiveLine (ZMod N)) :
    projLineAct N (M * M') P = projLineAct N M' (projLineAct N M P) := by
  have hmul : redMat N (M * M') = redMat N M * redMat N M' := by
    rw [redMat, redMat, redMat, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply,
      ← RingHom.mapMatrix_apply, map_mul]
  have hMM' : IsUnit (redMat N (M * M')).det := by
    rw [hmul, Matrix.det_mul]
    exact hM.mul hM'
  rw [projLineAct_of_isUnit N _ hMM', projLineAct_of_isUnit N _ hM, projLineAct_of_isUnit N _ hM']
  have hMM'2 : IsUnit (redMat N M * redMat N M').det := by rw [← hmul]; exact hMM'
  rw [show ProjectiveLine.vecMul (redMat N (M * M')) hMM' = ProjectiveLine.vecMul _ hMM'2 from by
    congr 1]
  exact ProjectiveLine.vecMul_mul _ _ hM hM' hMM'2 P

theorem projLineAct_coe_mul (N : ℕ) (g h : SL(2, ℤ)) (P : ProjectiveLine (ZMod N)) :
    projLineAct N ((g * h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) P
      = projLineAct N (h : Matrix (Fin 2) (Fin 2) ℤ) (projLineAct N (g : Matrix (Fin 2) (Fin 2) ℤ) P) := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  exact projLineAct_mul N _ _ (isUnit_det_redMat_coe N g) (isUnit_det_redMat_coe N h) P

section Rep

variable (N : ℕ) (K : Type*) [CommRing K]

noncomputable def projLineRepSL : Representation K SL(2, ℤ) (ProjectiveLine (ZMod N) → K) where
  toFun g := LinearMap.funLeft K K (projLineAct N (g : Matrix (Fin 2) (Fin 2) ℤ))
  map_one' := by
    apply LinearMap.ext
    intro f
    funext P
    simp [LinearMap.funLeft_apply, projLineAct_one]
  map_mul' g h := by
    apply LinearMap.ext
    intro f
    funext P
    simp only [LinearMap.funLeft_apply, Module.End.mul_apply, projLineAct_coe_mul]

@[simp]
theorem projLineRepSL_apply (g : SL(2, ℤ)) (f : ProjectiveLine (ZMod N) → K) (P : ProjectiveLine (ZMod N)) :
    projLineRepSL N K g f P = f (projLineAct N (g : Matrix (Fin 2) (Fin 2) ℤ) P) :=
  rfl

noncomputable def projLineRep :
    Representation K (CongruenceSubgroup.Gamma0 1) (ProjectiveLine (ZMod N) → K) :=
  (projLineRepSL N K).comp (CongruenceSubgroup.Gamma0 1).subtype

@[simp]
theorem projLineRep_apply (g : CongruenceSubgroup.Gamma0 1) (f : ProjectiveLine (ZMod N) → K)
    (P : ProjectiveLine (ZMod N)) :
    projLineRep N K g f P = f (projLineAct N ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) P) :=
  rfl

noncomputable def projLineAlphaAdj (ℓ : ℕ) :
    (ProjectiveLine (ZMod N) → K) →ₗ[K] (ProjectiveLine (ZMod N) → K) :=
  LinearMap.funLeft K K (projLineAct N !![(ℓ : ℤ), 0; 0, 1])

@[simp]
theorem projLineAlphaAdj_apply (ℓ : ℕ) (f : ProjectiveLine (ZMod N) → K) (P : ProjectiveLine (ZMod N)) :
    projLineAlphaAdj N K ℓ f P = f (projLineAct N !![(ℓ : ℤ), 0; 0, 1] P) :=
  rfl

end Rep

noncomputable def projLineFixedCard (N : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ) : ℕ :=
  Nat.card {P : ProjectiveLine (ZMod N) // projLineAct N M P = P}

def projLineCuspSetoid (N : ℕ) : Setoid (ProjectiveLine (ZMod N)) :=
  Relation.EqvGen.setoid fun P Q => projLineAct N !![1, 1; 0, 1] P = Q

def ProjLineCusps (N : ℕ) : Type _ :=
  Quotient (projLineCuspSetoid N)

def projLineCuspMk (N : ℕ) (P : ProjectiveLine (ZMod N)) : ProjLineCusps N :=
  Quotient.mk (projLineCuspSetoid N) P

noncomputable def fixedCuspCount (N : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ) : ℕ :=
  Nat.card {c : ProjLineCusps N //
    ∀ P : ProjectiveLine (ZMod N), projLineCuspMk N P = c → projLineCuspMk N (projLineAct N M P) = c}

end HeckeEis
