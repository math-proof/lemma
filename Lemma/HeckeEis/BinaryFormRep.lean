import Mathlib
import Lemma.ProjectiveLineMatrixAction.Main
import Abbrev.HeckeEis_BinaryFormRep

namespace HeckeEis

open MvPolynomial ModularCurve
open scoped MatrixGroups

theorem eval_smul_of_isHomogeneous {σ : Type*} {R : Type*} [CommRing R] {φ : MvPolynomial σ R} {n : ℕ}
    (hφ : φ.IsHomogeneous n) (c : R) (x : σ → R) :
    MvPolynomial.eval (c • x) φ = c ^ n * MvPolynomial.eval x φ := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = n := by
    have h := hφ (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.degree, Finsupp.weight, Finsupp.sum, Finsupp.linearCombination, Finsupp.lsum] using h
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

section BinaryForms

variable (K : Type*) [CommRing K]

noncomputable def binarySubst (M : Matrix (Fin 2) (Fin 2) ℤ) :
    MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K :=
  MvPolynomial.aeval fun j => ∑ i : Fin 2, C ((M i j : ℤ) : K) * X i

theorem binarySubst_X (M : Matrix (Fin 2) (Fin 2) ℤ) (j : Fin 2) :
    binarySubst K M (X j) = ∑ i : Fin 2, C ((M i j : ℤ) : K) * X i :=
  MvPolynomial.aeval_X _ _

theorem binarySubst_C (M : Matrix (Fin 2) (Fin 2) ℤ) (r : K) : binarySubst K M (C r) = C r := by
  rw [binarySubst, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

theorem binarySubst_one : binarySubst K (1 : Matrix (Fin 2) (Fin 2) ℤ) = AlgHom.id K _ := by
  refine MvPolynomial.algHom_ext fun j => ?_
  rw [binarySubst_X, AlgHom.id_apply, Fin.sum_univ_two]
  fin_cases j <;> simp [Matrix.one_apply]

theorem binarySubst_mul (M M' : Matrix (Fin 2) (Fin 2) ℤ) :
    binarySubst K (M * M') = (binarySubst K M).comp (binarySubst K M') := by
  refine MvPolynomial.algHom_ext fun j => ?_
  rw [AlgHom.comp_apply, binarySubst_X, binarySubst_X]
  simp only [Fin.sum_univ_two, Matrix.mul_apply, map_add, map_mul, binarySubst_C, binarySubst_X,
    Int.cast_add, Int.cast_mul, C_mul]
  ring

theorem binarySubst_mem {n : ℕ} (M : Matrix (Fin 2) (Fin 2) ℤ) {F : MvPolynomial (Fin 2) K}
    (hF : F ∈ BinaryForm K n) : binarySubst K M F ∈ BinaryForm K n := by
  rw [MvPolynomial.mem_homogeneousSubmodule] at hF ⊢
  have h := hF.aeval (fun j => ∑ i : Fin 2, C ((M i j : ℤ) : K) * X i)
    (fun j => MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => (MvPolynomial.isHomogeneous_X K i).C_mul _)
  simpa only [binarySubst, one_mul] using h

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

@[simp]
theorem binaryFormRepSL_apply_coe (g : SL(2, ℤ)) (F : BinaryForm K n) :
    ((binaryFormRepSL K n g F : BinaryForm K n) : MvPolynomial (Fin 2) K)
      = binarySubst K (g : Matrix (Fin 2) (Fin 2) ℤ) F :=
  rfl

noncomputable def binaryFormAlphaAdj (ℓ : ℕ) : BinaryForm K n →ₗ[K] BinaryForm K n :=
  (binarySubst K !![(ℓ : ℤ), 0; 0, 1]).toLinearMap.restrict fun F hF => binarySubst_mem K _ hF

@[simp]
theorem binaryFormAlphaAdj_apply_coe (ℓ : ℕ) (F : BinaryForm K n) :
    ((binaryFormAlphaAdj K n ℓ F : BinaryForm K n) : MvPolynomial (Fin 2) K)
      = binarySubst K !![(ℓ : ℤ), 0; 0, 1] F :=
  rfl

end BinaryForms

section Eval

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K] [CharP K p]

noncomputable def evalRow (F : MvPolynomial (Fin 2) K) (v : UnimodularRow (ZMod p)) : K :=
  MvPolynomial.eval ![ZMod.castHom (dvd_refl p) K v.1.1, ZMod.castHom (dvd_refl p) K v.1.2] F

theorem evalRow_eq_of_unit_mul {F : MvPolynomial (Fin 2) K} (hF : F ∈ BinaryForm K (p - 1))
    (u : (ZMod p)ˣ) (v w : UnimodularRow (ZMod p))
    (h1 : (u : ZMod p) * v.1.1 = w.1.1) (h2 : (u : ZMod p) * v.1.2 = w.1.2) :
    evalRow p K F w = evalRow p K F v := by
  have hu : (ZMod.castHom (dvd_refl p) K (u : ZMod p)) ^ (p - 1) = 1 := by
    rw [← map_pow, ZMod.pow_card_sub_one_eq_one (Units.ne_zero u), map_one]
  have hvec : (![ZMod.castHom (dvd_refl p) K w.1.1, ZMod.castHom (dvd_refl p) K w.1.2] : Fin 2 → K)
      = (ZMod.castHom (dvd_refl p) K (u : ZMod p)) •
          ![ZMod.castHom (dvd_refl p) K v.1.1, ZMod.castHom (dvd_refl p) K v.1.2] := by
    funext i
    fin_cases i <;> simp [← h1, ← h2, map_mul]
  unfold evalRow
  rw [hvec, eval_smul_of_isHomogeneous ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hF), hu, one_mul]

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

@[simp]
theorem binaryFormEval_mk (F : BinaryForm K (p - 1)) (v : UnimodularRow (ZMod p)) :
    binaryFormEval p K F (⟦v⟧ : ProjectiveLine (ZMod p)) = evalRow p K F v :=
  rfl

end Eval

end HeckeEis
