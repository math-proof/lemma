import Lemma.Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Lemma.Definitions.Def_NumberField_IdeleProductMeasure

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory AutomorphicForm

noncomputable section

namespace LanglandsTunnell.CubicInduction

section Furniture

variable {A : Type*} [CommRing A]

def lowerUnipotent21 (x : A) : GL (Fin 3) A where
  val := !![1, 0, 0; x, 1, 0; 0, 0, 1]
  inv := !![1, 0, 0; -x, 1, 0; 0, 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

@[simp] theorem lowerUnipotent21_coe (x : A) :
    ((lowerUnipotent21 x : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = !![1, 0, 0; x, 1, 0; 0, 0, 1] :=
  rfl

def longWeyl3 : GL (Fin 3) A where
  val := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  inv := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

@[simp] theorem longWeyl3_coe :
    ((longWeyl3 : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = !![0, 0, 1; 0, 1, 0; 1, 0, 0] :=
  rfl

def dualWhittakerFn3 {R : Type*} (W : GL (Fin 3) A → R) : GL (Fin 3) A → R :=
  fun g => W (longWeyl3 * transposeInv3 g)

theorem dualWhittakerFn3_apply {R : Type*} (W : GL (Fin 3) A → R) (g : GL (Fin 3) A) :
    dualWhittakerFn3 W g = W (longWeyl3 * transposeInv3 g) :=
  rfl

def weylPrime3 : GL (Fin 3) A where
  val := !![1, 0, 0; 0, 0, 1; 0, 1, 0]
  inv := !![1, 0, 0; 0, 0, 1; 0, 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

@[simp] theorem weylPrime3_coe :
    ((weylPrime3 : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = !![1, 0, 0; 0, 0, 1; 0, 1, 0] :=
  rfl

theorem weylPrime3_mul_self : (weylPrime3 : GL (Fin 3) A) * weylPrime3 = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

theorem weylPrime3_inv : (weylPrime3 : GL (Fin 3) A)⁻¹ = weylPrime3 :=
  inv_eq_of_mul_eq_one_right weylPrime3_mul_self

theorem transposeInv3_weylPrime3 : transposeInv3 (weylPrime3 : GL (Fin 3) A) = weylPrime3 := by
  refine Units.ext ?_
  change (((weylPrime3 : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  rw [weylPrime3_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]

theorem weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3 (v : Fin 2 → A) :
    ((weylPrime3 * transposeInv3 (radicalP21 v) * weylPrime3 : GL (Fin 3) A) :
        Matrix (Fin 3) (Fin 3) A) = !![1, 0, 0; -(v 0), 1, -(v 1); 0, 0, 1] := by
  have hinv : (((radicalP21 v : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![1, 0, -(v 0); 0, 1, -(v 1); 0, 0, 1] := by
    rw [Matrix.coe_units_inv, radicalP21_coe]
    refine Matrix.inv_eq_left_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have htr : ((transposeInv3 (radicalP21 v) : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![1, 0, 0; 0, 1, 0; -(v 0), -(v 1), 1] := by
    change (((radicalP21 v : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
    rw [hinv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]
  rw [Units.val_mul, Units.val_mul, htr, weylPrime3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem transposeInv3_lowerUnipotent21 (x : A) :
    transposeInv3 (lowerUnipotent21 x) = upperUnipotent3 (-x) 0 0 := by
  refine Units.ext ?_
  have hinv : (((lowerUnipotent21 x : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![1, 0, 0; -x, 1, 0; 0, 0, 1] := by
    rw [Matrix.coe_units_inv, lowerUnipotent21_coe]
    refine Matrix.inv_eq_left_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  change (((lowerUnipotent21 x : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  rw [hinv, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]

end Furniture

section Global

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

def globalZeta31 (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (s : ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : ℂ :=
  letI := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  ∫ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      (∫ x : AdeleRing (𝓞 ℚ) ℚ, W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g)
          ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) *
        ((χ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1)
    ∂(NumberField.Idele.idelicHaar ℚ)

def globalZeta30 (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (s : ℂ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) : ℂ :=
  ∫ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) *
        ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1)
    ∂(NumberField.Idele.idelicHaar ℚ)

def globalZetaDual31 (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (s : ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : ℂ :=
  globalZeta31 (dualWhittakerFn3 W) χ⁻¹ s (weylPrime3 * transposeInv3 g)

end Global

end LanglandsTunnell.CubicInduction

end

#check @LanglandsTunnell.CubicInduction.lowerUnipotent21
#check @LanglandsTunnell.CubicInduction.longWeyl3
#check @LanglandsTunnell.CubicInduction.dualWhittakerFn3
#check @LanglandsTunnell.CubicInduction.globalZeta31
#check @LanglandsTunnell.CubicInduction.weylPrime3
#check @LanglandsTunnell.CubicInduction.globalZeta30
#check @LanglandsTunnell.CubicInduction.globalZetaDual31
#print axioms LanglandsTunnell.CubicInduction.weylPrime3_mul_self
#print axioms LanglandsTunnell.CubicInduction.transposeInv3_weylPrime3
#print axioms LanglandsTunnell.CubicInduction.weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3
#print axioms LanglandsTunnell.CubicInduction.transposeInv3_lowerUnipotent21
#print axioms LanglandsTunnell.CubicInduction.globalZeta30
#print axioms LanglandsTunnell.CubicInduction.globalZetaDual31
#print axioms LanglandsTunnell.CubicInduction.globalZeta31
