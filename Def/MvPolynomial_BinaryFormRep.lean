module
public import Mathlib
public import Def.Matrix_ProjectiveLineMatrixAction
public import Abbrev.HeckeEis_BinaryFormRep


public section

namespace HeckeEis

open MvPolynomial ModularCurve SpecialLinearGroup
open scoped MatrixGroups

section BinaryForms

variable (K : Type*) [CommRing K]

noncomputable def binarySubst (M : Matrix (Fin 2) (Fin 2) ℤ) :
    MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K :=
  MvPolynomial.aeval fun j => ∑ i : Fin 2, C ((M i j : ℤ) : K) * X i

variable (n : ℕ)

noncomputable def binaryFormRepSL : Representation K SL(2, ℤ) (BinaryForm K n) where
  toFun g := (binarySubst K (g : Matrix (Fin 2) (Fin 2) ℤ)).toLinearMap.restrict
    fun F hF => binarySubst_mem K _ hF
  map_one' := by
    refine LinearMap.ext fun F => Subtype.ext ?_
    change binarySubst K ((1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) F.1 = F.1
    rw [Matrix.SpecialLinearGroup.coe_one, binarySubst_one]
    rfl
  map_mul' g h := by
    refine LinearMap.ext fun F => Subtype.ext ?_
    change binarySubst K ((g * h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) F.1
      = binarySubst K (g : Matrix (Fin 2) (Fin 2) ℤ) (binarySubst K (h : Matrix (Fin 2) (Fin 2) ℤ) F.1)
    rw [Matrix.SpecialLinearGroup.coe_mul, binarySubst_mul]
    rfl

noncomputable def binaryFormAlphaAdj (ℓ : ℕ) : BinaryForm K n →ₗ[K] BinaryForm K n :=
  (binarySubst K !![(ℓ : ℤ), 0; 0, 1]).toLinearMap.restrict fun F hF => binarySubst_mem K _ hF

end BinaryForms

section Eval

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K] [CharP K p]

noncomputable def evalRow (F : MvPolynomial (Fin 2) K) (v : UnimodularRow (ZMod p)) : K :=
  MvPolynomial.eval ![ZMod.castHom (dvd_refl p) K v.1.1, ZMod.castHom (dvd_refl p) K v.1.2] F

noncomputable def binaryFormEval : BinaryForm K (p - 1) →ₗ[K] (ProjectiveLine (ZMod p) → K) where
  toFun F := Quotient.lift (evalRow p K (F : MvPolynomial (Fin 2) K)) fun v w hvw => by
    obtain ⟨u, h1, h2⟩ := hvw
    exact (evalRow_eq_of_unit_mul p K F.2 u v w h1 h2).symm
  map_add' F G := by
    funext P
    induction P using Quotient.inductionOn with
    | h v =>
      change evalRow p K ((F + G : BinaryForm K (p - 1)) : MvPolynomial (Fin 2) K) v
        = evalRow p K (F : MvPolynomial (Fin 2) K) v + evalRow p K (G : MvPolynomial (Fin 2) K) v
      simp [evalRow]
  map_smul' c F := by
    funext P
    induction P using Quotient.inductionOn with
    | h v =>
      change evalRow p K ((c • F : BinaryForm K (p - 1)) : MvPolynomial (Fin 2) K) v
        = c • evalRow p K (F : MvPolynomial (Fin 2) K) v
      simp [evalRow, MvPolynomial.smul_eval]

end Eval

end HeckeEis
