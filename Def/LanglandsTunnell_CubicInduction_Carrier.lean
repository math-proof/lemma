module

public import Def.AutomorphicForm_AdelicLsXi
public import Def.AutomorphicForm_ConstantTerm
public import Theorem.Matrix.AdelicLevel
public import Abbrev.LanglandsTunnell_CubicInduction_Carrier

@[expose] public section

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

def radicalP21 (v : Fin 2 → A) : GL (Fin 3) A :=
  upperUnipotent3 0 (v 1) (v 0)

def radicalP12 (v : Fin 2 → A) : GL (Fin 3) A :=
  upperUnipotent3 (v 0) 0 (v 1)

end Unipotent

section Iota

variable {A : Type*} [CommRing A]

def embedMat2 (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 3) (Fin 3) A :=
  !![M 0 0, M 0 1, 0; M 1 0, M 1 1, 0; 0, 0, 1]

def iotaGL : GL (Fin 2) A →* GL (Fin 3) A where
  toFun h :=
    { val := embedMat2 h
      inv := embedMat2 ((h⁻¹ : GL (Fin 2) A) : Matrix _ _ _)
      val_inv := by rw [← embedMat2_mul, Units.mul_inv, embedMat2_one]
      inv_val := by rw [← embedMat2_mul, Units.inv_mul, embedMat2_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact embedMat2_one)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact embedMat2_mul _ _)

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

def iota : AutomorphicForm.AdelicGL2 R K →* AdelicGL 3 R K :=
  iotaGL (A := AdeleRing R K)

def mirabolicRep (c : MirabolicIndex K) : GL (Fin 2) K :=
  c.out

end Iota

section LocalCompact

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

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

end
