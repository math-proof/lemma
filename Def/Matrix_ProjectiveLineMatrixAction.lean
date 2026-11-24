module
public import Mathlib
public import Def.ModularCurve_ProjectiveLine
public import Instance.ProjectiveLineMatrixAction
public import Abbrev.ProjectiveLineMatrixAction


public section

namespace SpecialLinearGroup.ProjectiveLine

variable {R : Type*} [CommRing R]

def vecMulRow (M : Matrix (Fin 2) (Fin 2) R) (hM : IsUnit M.det) (v : UnimodularRow R) :
    UnimodularRow R :=
  ⟨(v.1.1 * M 0 0 + v.1.2 * M 1 0, v.1.1 * M 0 1 + v.1.2 * M 1 1), by
    obtain ⟨x, y, h⟩ := v.2
    obtain ⟨e, he⟩ := hM.exists_left_inv
    rw [Matrix.det_fin_two] at he
    exact ⟨e * (x * M 1 1 - y * M 0 1), e * (y * M 0 0 - x * M 1 0), by
      linear_combination (x * v.1.1 + y * v.1.2) * he + h⟩⟩

def vecMul (M : Matrix (Fin 2) (Fin 2) R) (hM : IsUnit M.det) : ProjectiveLine R → ProjectiveLine R :=
  Quotient.map (vecMulRow M hM) <| by
    rintro v w ⟨u, h1, h2⟩
    refine ⟨u, ?_, ?_⟩
    · simp only [vecMulRow_fst]
      linear_combination M 0 0 * h1 + M 1 0 * h2
    · simp only [vecMulRow_snd]
      linear_combination M 0 1 * h1 + M 1 1 * h2

end SpecialLinearGroup.ProjectiveLine

namespace HeckeEis

open ModularCurve SpecialLinearGroup
open scoped MatrixGroups

noncomputable def projLineAct (N : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ) :
    ProjectiveLine (ZMod N) → ProjectiveLine (ZMod N) :=
  if h : IsUnit (redMat N M).det then ProjectiveLine.vecMul (redMat N M) h else id

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

noncomputable def projLineRep :
    Representation K (CongruenceSubgroup.Gamma0 1) (ProjectiveLine (ZMod N) → K) :=
  (projLineRepSL N K).comp (CongruenceSubgroup.Gamma0 1).subtype

noncomputable def projLineAlphaAdj (ℓ : ℕ) :
    (ProjectiveLine (ZMod N) → K) →ₗ[K] (ProjectiveLine (ZMod N) → K) :=
  LinearMap.funLeft K K (projLineAct N !![(ℓ : ℤ), 0; 0, 1])

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
