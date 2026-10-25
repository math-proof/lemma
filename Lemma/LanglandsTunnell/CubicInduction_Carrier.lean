import Def.AutomorphicForm_AdelicLsXi
import Def.AutomorphicForm_ConstantTerm
import Lemma.NumberField.AdelicLevel
import Abbrev.LanglandsTunnell_CubicInduction_Carrier

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace LanglandsTunnell.CubicInduction

section Carrier

variable (n : ℕ) (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

def globalPointsGL : Matrix.GeneralLinearGroup (Fin n) K →* AdelicGL n R K :=
  Matrix.GeneralLinearGroup.map (algebraMap K (AdeleRing R K))

def centralScalarGL : (AdeleRing R K)ˣ →* AdelicGL n R K :=
  Matrix.GeneralLinearGroup.scalar (Fin n)

end Carrier

section Unipotent

variable {A : Type*} [CommRing A]

def upperUnipotent3 (x y z : A) : GL (Fin 3) A where
  val := !![1, x, z; 0, 1, y; 0, 0, 1]
  inv := !![1, -x, x * y - z; 0, 1, -y; 0, 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    all_goals ring
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    all_goals ring

@[simp] theorem upperUnipotent3_coe (x y z : A) :
    (upperUnipotent3 x y z : Matrix (Fin 3) (Fin 3) A) = !![1, x, z; 0, 1, y; 0, 0, 1] := rfl

@[simp] theorem upperUnipotent3_zero : upperUnipotent3 (0 : A) 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3]

def radicalP21 (v : Fin 2 → A) : GL (Fin 3) A :=
  upperUnipotent3 0 (v 1) (v 0)

def radicalP12 (v : Fin 2 → A) : GL (Fin 3) A :=
  upperUnipotent3 (v 0) 0 (v 1)

@[simp] theorem radicalP21_zero : radicalP21 (0 : Fin 2 → A) = 1 := by
  simp [radicalP21]

@[simp] theorem radicalP12_zero : radicalP12 (0 : Fin 2 → A) = 1 := by
  simp [radicalP12]

@[simp] theorem radicalP21_coe (v : Fin 2 → A) :
    (radicalP21 v : Matrix (Fin 3) (Fin 3) A) = !![1, 0, v 0; 0, 1, v 1; 0, 0, 1] := rfl

@[simp] theorem radicalP12_coe (v : Fin 2 → A) :
    (radicalP12 v : Matrix (Fin 3) (Fin 3) A) = !![1, v 0, v 1; 0, 1, 0; 0, 0, 1] := rfl

theorem radicalP21_add (v w : Fin 2 → A) : radicalP21 (v + w) = radicalP21 v * radicalP21 w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radicalP21, upperUnipotent3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, add_comm]

theorem radicalP12_add (v w : Fin 2 → A) : radicalP12 (v + w) = radicalP12 v * radicalP12 w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radicalP12, upperUnipotent3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, add_comm]

end Unipotent

section Iota

variable {A : Type*} [CommRing A]

def embedMat2 (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 3) (Fin 3) A :=
  !![M 0 0, M 0 1, 0; M 1 0, M 1 1, 0; 0, 0, 1]

theorem embedMat2_one : embedMat2 (1 : Matrix (Fin 2) (Fin 2) A) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2]

theorem embedMat2_mul (M N : Matrix (Fin 2) (Fin 2) A) :
    embedMat2 (M * N) = embedMat2 M * embedMat2 N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

def iotaGL : GL (Fin 2) A →* GL (Fin 3) A where
  toFun h :=
    { val := embedMat2 h
      inv := embedMat2 ((h⁻¹ : GL (Fin 2) A) : Matrix _ _ _)
      val_inv := by rw [← embedMat2_mul, Units.mul_inv, embedMat2_one]
      inv_val := by rw [← embedMat2_mul, Units.inv_mul, embedMat2_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact embedMat2_one)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact embedMat2_mul _ _)

@[simp] theorem coe_iotaGL (h : GL (Fin 2) A) :
    ((iotaGL h : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = embedMat2 h := rfl

theorem iotaGL_unipotentGL2 (x : A) :
    iotaGL (AutomorphicForm.unipotentGL2 x) = upperUnipotent3 x 0 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, upperUnipotent3]

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

def iota : AutomorphicForm.AdelicGL2 R K →* AdelicGL 3 R K :=
  iotaGL (A := AdeleRing R K)

def mirabolicRep (c : MirabolicIndex K) : GL (Fin 2) K :=
  c.out

theorem mirabolicRep_spec (c : MirabolicIndex K) :
    Quotient.mk _ (mirabolicRep K c) = c :=
  c.out_eq

theorem mirabolic_mk_unipotent_mul (x : K) (g : GL (Fin 2) K) :
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

theorem valued_one_entry_le3 (i j : Fin 3) :
    Valued.v ((1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j) ≤ 1 := by
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne h, map_zero]
    exact zero_le

theorem valued_mul_apply_le3 {C : WithZero (Multiplicative ℤ)}
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

def localMaximalCompact3 : Subgroup (GL (Fin 3) (v.adicCompletion K)) where
  carrier := {k | (∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j) ≤ 1) ∧
    (∀ i j, Valued.v (((k⁻¹ : GL (Fin 3) (v.adicCompletion K)) :
      Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j) ≤ 1)}
  one_mem' := by
    constructor
    · intro i j
      rw [Units.val_one]
      exact valued_one_entry_le3 R K v i j
    · intro i j
      rw [inv_one, Units.val_one]
      exact valued_one_entry_le3 R K v i j
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    constructor
    · intro i j
      rw [Units.val_mul]
      exact valued_mul_apply_le3 R K v (fun l => ha i l) (fun l => hb l j)
    · intro i j
      rw [_root_.mul_inv_rev, Units.val_mul]
      exact valued_mul_apply_le3 R K v (fun l => hb' i l) (fun l => ha' l j)
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨ha', ?_⟩
    intro i j
    rw [inv_inv]
    exact ha i j

theorem mem_localMaximalCompact3_iff {k : GL (Fin 3) (v.adicCompletion K)} :
    k ∈ localMaximalCompact3 R K v ↔
      (∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j) ≤ 1) ∧
      (∀ i j, Valued.v (((k⁻¹ : GL (Fin 3) (v.adicCompletion K)) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j) ≤ 1) :=
  Iff.rfl

theorem not_mem_localMaximalCompact3_of_entry {k : GL (Fin 3) (v.adicCompletion K)} {i j : Fin 3}
    (h : 1 < Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j)) :
    k ∉ localMaximalCompact3 R K v :=
  fun hk => not_le_of_gt h (hk.1 i j)

theorem not_mem_localMaximalCompact3_of_inv_entry {k : GL (Fin 3) (v.adicCompletion K)} {i j : Fin 3}
    (h : 1 < Valued.v (((k⁻¹ : GL (Fin 3) (v.adicCompletion K)) :
      Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j)) :
    k ∉ localMaximalCompact3 R K v :=
  fun hk => not_le_of_gt h (hk.2 i j)

end LocalCompact

section Components

variable (ι : Type*) [Fintype ι] [DecidableEq ι]
variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

variable (v : HeightOneSpectrum R)

def componentAtN : GL ι (AdeleRing R K) →* GL ι (v.adicCompletion K) :=
  Matrix.GeneralLinearGroup.map ((AdelicLevel.finAdeleEval R K v).comp (AdelicLevel.adeleFin R K))

def archComponentN : GL ι (AdeleRing R K) →* GL ι (InfiniteAdeleRing K) :=
  Matrix.GeneralLinearGroup.map (AdelicLevel.adeleArch R K)

end Components

section Three

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

abbrev componentAt3 : AdelicGL 3 R K →* GL (Fin 3) (v.adicCompletion K) :=
  componentAtN (Fin 3) R K v

abbrev archComponent3 : AdelicGL 3 R K →* GL (Fin 3) (InfiniteAdeleRing K) :=
  archComponentN (Fin 3) R K

end Three

end LanglandsTunnell.CubicInduction
