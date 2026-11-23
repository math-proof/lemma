module

public import Def.AutomorphicForm_AdelicLsXi
public import Def.AutomorphicForm_ConstantTerm
public import Theorem.Matrix.AdelicLevel
public import Abbrev.LanglandsTunnell_CubicInduction_Carrier

public noncomputable section

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace LanglandsTunnell.CubicInduction

section Carrier

variable (n : ℕ) (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]


@[simp] public theorem upperUnipotent3_coe (x y z : A) :
    (upperUnipotent3 x y z : Matrix (Fin 3) (Fin 3) A) = !![1, x, z; 0, 1, y; 0, 0, 1] := rfl


@[simp] public theorem upperUnipotent3_zero : upperUnipotent3 (0 : A) 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3]


@[simp] public theorem radicalP21_zero : radicalP21 (0 : Fin 2 → A) = 1 := by
  simp [radicalP21]


@[simp] public theorem radicalP12_zero : radicalP12 (0 : Fin 2 → A) = 1 := by
  simp [radicalP12]


@[simp] public theorem radicalP21_coe (v : Fin 2 → A) :
    (radicalP21 v : Matrix (Fin 3) (Fin 3) A) = !![1, 0, v 0; 0, 1, v 1; 0, 0, 1] := rfl


@[simp] public theorem radicalP12_coe (v : Fin 2 → A) :
    (radicalP12 v : Matrix (Fin 3) (Fin 3) A) = !![1, v 0, v 1; 0, 1, 0; 0, 0, 1] := rfl


public theorem radicalP21_add (v w : Fin 2 → A) : radicalP21 (v + w) = radicalP21 v * radicalP21 w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radicalP21, upperUnipotent3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, add_comm]


public theorem radicalP12_add (v w : Fin 2 → A) : radicalP12 (v + w) = radicalP12 v * radicalP12 w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radicalP12, upperUnipotent3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, add_comm]

end Unipotent

section Iota

variable {A : Type*} [CommRing A]


public theorem embedMat2_one : embedMat2 (1 : Matrix (Fin 2) (Fin 2) A) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2]


public theorem embedMat2_mul (M N : Matrix (Fin 2) (Fin 2) A) :
    embedMat2 (M * N) = embedMat2 M * embedMat2 N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]


@[simp] public theorem coe_iotaGL (h : GL (Fin 2) A) :
    ((iotaGL h : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = embedMat2 h := rfl


public theorem iotaGL_unipotentGL2 (x : A) :
    iotaGL (AutomorphicForm.unipotentGL2 x) = upperUnipotent3 x 0 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, upperUnipotent3]

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]


public theorem mirabolicRep_spec (c : MirabolicIndex K) :
    Quotient.mk _ (mirabolicRep K c) = c :=
  c.out_eq


public theorem mirabolic_mk_unipotent_mul (x : K) (g : GL (Fin 2) K) :
    (Quotient.mk _ (AutomorphicForm.unipotentGL2 x * g) : MirabolicIndex K) = Quotient.mk _ g := by
  have h : g * (AutomorphicForm.unipotentGL2 x * g)⁻¹ ∈
      (AutomorphicForm.unipotentGL2Hom (R := K)).range := by
    rw [_root_.mul_inv_rev, mul_inv_cancel_left]
    exact inv_mem ⟨Multiplicative.ofAdd x, rfl⟩
  exact Quotient.sound (QuotientGroup.rightRel_apply.mpr h)

end Iota

section LocalCompact

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)


public theorem valued_one_entry_le3 (i j : Fin 3) :
    Valued.v ((1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j) ≤ 1 := by
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne h, map_zero]
    exact zero_le


public theorem valued_mul_apply_le3 {C : WithZero (Multiplicative ℤ)}
    {a b : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)} {i j : Fin 3}
    (ha : ∀ l, Valued.v (a i l) ≤ C) (hb : ∀ l, Valued.v (b l j) ≤ 1) :
    Valued.v ((a * b) i j) ≤ C := by
  have hterm : ∀ l, Valued.v (a i l * b l j) ≤ C := fun l => by
    rw [map_mul]
    calc Valued.v (a i l) * Valued.v (b l j) ≤ Valued.v (a i l) * 1 :=
          mul_le_mul_right (hb l) _
      _ = Valued.v (a i l) := mul_one _
      _ ≤ C := ha l
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hterm 2))
  exact le_trans (Valuation.map_add _ _ _) (max_le (hterm 0) (hterm 1))


public theorem mem_localMaximalCompact3_iff {k : GL (Fin 3) (v.adicCompletion K)} :
    k ∈ localMaximalCompact3 R K v ↔
      (∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j) ≤ 1) ∧
      (∀ i j, Valued.v (((k⁻¹ : GL (Fin 3) (v.adicCompletion K)) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j) ≤ 1) :=
  Iff.rfl


public theorem not_mem_localMaximalCompact3_of_entry {k : GL (Fin 3) (v.adicCompletion K)} {i j : Fin 3}
    (h : 1 < Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j)) :
    k ∉ localMaximalCompact3 R K v :=
  fun hk => not_le_of_gt h (hk.1 i j)


public theorem not_mem_localMaximalCompact3_of_inv_entry {k : GL (Fin 3) (v.adicCompletion K)} {i j : Fin 3}
    (h : 1 < Valued.v (((k⁻¹ : GL (Fin 3) (v.adicCompletion K)) :
      Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j)) :
    k ∉ localMaximalCompact3 R K v :=
  fun hk => not_le_of_gt h (hk.2 i j)

end LocalCompact

section Components

variable (ι : Type*) [Fintype ι] [DecidableEq ι]
variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

variable (v : HeightOneSpectrum R)

