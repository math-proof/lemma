import Def.NumberField_AdelicLevel
import Instance.NumberField_AdelicHaar
import Structure.NumberField_AdelicLevel

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel RestrictedProduct Matrix
open scoped Topology

noncomputable section

namespace Matrix.AdelicLevel

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]


section Projections

def finAdeleEval (v : HeightOneSpectrum R) : FiniteAdeleRing R K →+* v.adicCompletion K where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def adeleFin : AdeleRing R K →+* FiniteAdeleRing R K where
  toFun a := a.2
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def finComponent (v : HeightOneSpectrum R) :
    GL (Fin 2) (FiniteAdeleRing R K) →* GL (Fin 2) (v.adicCompletion K) :=
  Matrix.GeneralLinearGroup.map (finAdeleEval R K v)

def glFin : GL (Fin 2) (AdeleRing R K) →* GL (Fin 2) (FiniteAdeleRing R K) :=
  Matrix.GeneralLinearGroup.map (adeleFin R K)

end Projections


section FiniteLevel


variable {R K}
variable {N : Ideal R}

variable {m m' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)}

variable {m m' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)}

variable (R K) (N)

def finiteLevelZero : Subgroup (GL (Fin 2) (FiniteAdeleRing R K)) where
  carrier := {g | IsLevelZeroMatrix R K N (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) ∧
    IsLevelZeroMatrix R K N ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix _ _ _)}
  one_mem' := ⟨by rw [Units.val_one]; exact .one, by rw [inv_one, Units.val_one]; exact .one⟩
  mul_mem' ha hb := ⟨by rw [Units.val_mul]; exact ha.1.mul hb.1,
    by simpa [Units.val_mul, Units.val_inv, mul_inv_rev] using hb.2.mul ha.2⟩
  inv_mem' ha := ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

def finiteLevelOne : Subgroup (GL (Fin 2) (FiniteAdeleRing R K)) where
  carrier := {g | IsLevelOneMatrix R K N (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) ∧
    IsLevelOneMatrix R K N ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix _ _ _)}
  one_mem' := ⟨by rw [Units.val_one]; exact .one, by rw [inv_one, Units.val_one]; exact .one⟩
  mul_mem' ha hb := ⟨by rw [Units.val_mul]; exact ha.1.mul hb.1,
    by simpa [Units.val_mul, Units.val_inv, mul_inv_rev] using hb.2.mul ha.2⟩
  inv_mem' ha := ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

variable {R K N}

variable (R K N)

abbrev finiteIntegralGL2 : Subgroup (GL (Fin 2) (FiniteAdeleRing R K)) := finiteLevelZero R K ⊤


end FiniteLevel

section Adelic

variable (N : Ideal R)

def levelZero : Subgroup (GL (Fin 2) (AdeleRing R K)) := (finiteLevelZero R K N).comap (glFin R K)

def levelOne : Subgroup (GL (Fin 2) (AdeleRing R K)) := (finiteLevelOne R K N).comap (glFin R K)

variable {R K N}

variable (R K N)


end Adelic

section Gen

def diagOne {A : Type*} [CommRing A] : Aˣ →* GL (Fin 2) A where
  toFun a :=
    { val := Matrix.diagonal ![(a : A), 1]
      inv := Matrix.diagonal ![((a⁻¹ : Aˣ) : A), 1]
      val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp
      inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp }
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by ext i j; fin_cases i <;> fin_cases j <;> simp

variable (v : HeightOneSpectrum R)

open scoped Classical in

open scoped Classical in
open scoped Classical in
def heckeGenAt : (v.adicCompletion K)ˣ →* GL (Fin 2) (AdeleRing R K) :=
  diagOne.comp ((Units.map (finIncl R K)).comp (localUnit R K v))

variable {R K v}

variable (K v)

variable (R)

def heckeGen : GL (Fin 2) (AdeleRing R K) := heckeGenAt R K v (uniformizerUnit K v)

variable {R K v}

end Gen

end Matrix.AdelicLevel

namespace NumberField.AdelicLevel
export Matrix.AdelicLevel (
  idealBound_bot idealBound_of_ne_bot idealBound_ne_zero idealBound_le_one
  idealBound_eq_one_of_not_dvd idealBound_top finite_setOf_idealBound_ne_one
  algebraMap_mem_adicCompletionIntegers valued_algebraMap setOf_valued_le_eq_preimage
  isOpen_setOf_valued_le isClosed_adicCompletionIntegers isClosed_setOf_valued_le
  exists_valued_eq_exp_neg isOpen_setOf_valued_le_idealBound isClosed_setOf_valued_le_idealBound
  archEval finAdeleEval adeleArch adeleFin archEval_apply finAdeleEval_apply adeleArch_apply
  adeleFin_apply continuous_archEval continuous_finAdeleEval continuous_adeleArch
  continuous_adeleFin archComponent finComponent glArch glFin archComponent_apply
  finComponent_apply glArch_apply glFin_apply continuous_archComponent continuous_finComponent
  continuous_glArch continuous_glFin coe_zero_apply coe_one_apply coe_add_apply coe_mul_apply
  coe_sub_apply coe_neg_apply idealBall_subset_integralFiniteAdeles zero_mem_idealBall
  isOpen_integralFiniteAdeles isClosed_integralFiniteAdeles isClosed_idealBall isOpen_idealBall
  isCompact_integralFiniteAdeles one_mem_integralFiniteAdeles zero_mem_integralFiniteAdeles
  add_mem_integralFiniteAdeles mul_mem_integralFiniteAdeles sub_mem_integralFiniteAdeles
  valued_apply_le_one add_mem_idealBall mul_mem_idealBall_left mul_mem_idealBall_right
  finiteLevelZero finiteLevelOne mem_finiteLevelZero_iff mem_finiteLevelOne_iff
  finiteLevelOne_le_finiteLevelZero finiteIntegralGL2 mem_finiteIntegralGL2_iff
  isClosed_setOf_isLevelZeroMatrix isClosed_setOf_isLevelOneMatrix isOpen_setOf_isLevelZeroMatrix
  isOpen_setOf_isLevelOneMatrix isOpen_finiteLevelZero isOpen_finiteLevelOne
  isClosed_finiteLevelZero isClosed_finiteLevelOne isCompact_setOf_integral
  isCompact_finiteLevelZero isCompact_finiteLevelOne levelZero levelOne mem_levelZero_iff
  mem_levelOne_iff levelOne_le_levelZero isOpen_levelZero isOpen_levelOne isClosed_levelZero
  isClosed_levelOne diagOne diagOne_coe_apply finIncl finIncl_apply_fst finIncl_apply_snd localUnit
  localUnit_apply_self localUnit_apply_of_ne heckeGenAt heckeGenAt_fst heckeGenAt_snd_apply_of_ne
  heckeGenAt_snd_apply_self heckeGenAt_inv_mul_heckeGenAt_mem_levelOne uniformizer
  intValuation_uniformizer valued_uniformizer uniformizerUnit valued_uniformizerUnit heckeGen
  heckeGen_inv_mul_heckeGenAt_mem_levelOne
)
end NumberField.AdelicLevel

namespace Matrix.AdelicLevel
export NumberField.AdelicLevel (idealBound integralFiniteAdeles idealBall
  IsLevelZeroMatrix IsLevelOneMatrix)
end Matrix.AdelicLevel

end
