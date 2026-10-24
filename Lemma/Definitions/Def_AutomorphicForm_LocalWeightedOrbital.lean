import Lemma.Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Lemma.Definitions.Def_AutomorphicForm_ConstantTerm
import Lemma.Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option autoImplicit false

open MeasureTheory
open LanglandsTunnell.CubicInduction (diagUnits2)

noncomputable section

namespace AutomorphicForm

namespace LocalWeightedOrbital

section Algebra

variable {A : Type*} [CommRing A]

def arg (k : GL (Fin 2) A) (a b : Aˣ) (x : A) : GL (Fin 2) A :=
  k⁻¹ * (diagUnits2 a b * unipotentGL2 x) * k

theorem arg_one (a b : Aˣ) (x : A) : arg 1 a b x = diagUnits2 a b * unipotentGL2 x := by
  simp [arg]

theorem diagUnits2_self (a : Aˣ) : diagUnits2 a a = Matrix.GeneralLinearGroup.scalar (Fin 2) a := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagUnits2, Matrix.GeneralLinearGroup.scalar]

theorem arg_self (k : GL (Fin 2) A) (a : Aˣ) (x : A) :
    arg k a a x = k⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 2) a * unipotentGL2 x) * k := by
  rw [arg, diagUnits2_self]

end Algebra

section Slice

variable {A : Type*} [CommRing A] [MeasurableSpace (GL (Fin 2) A)] (μK : Measure (GL (Fin 2) A))

def slice (f : GL (Fin 2) A → ℂ) (a b : Aˣ) (x : A) : ℂ :=
  ∫ k, f (arg k a b x) ∂μK

@[simp] theorem slice_zero_fun (a b : Aˣ) (x : A) : slice μK (fun _ => 0) a b x = 0 := by
  simp [slice]

theorem slice_const_mul (c : ℂ) (f : GL (Fin 2) A → ℂ) (a b : Aˣ) (x : A) :
    slice μK (fun g => c * f g) a b x = c * slice μK f a b x := by
  simp only [slice]
  exact integral_const_mul c _

def centralValue (f : GL (Fin 2) A → ℂ) (a : Aˣ) : ℂ :=
  ∫ k, f (k⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) a * k) ∂μK

@[simp] theorem centralValue_zero_fun (a : Aˣ) : centralValue μK (fun _ => 0) a = 0 := by
  simp [centralValue]

theorem centralValue_eq (f : GL (Fin 2) A → ℂ) (a : Aˣ) :
    centralValue μK f a = μK.real Set.univ • f (Matrix.GeneralLinearGroup.scalar (Fin 2) a) := by
  have hc : ∀ k : GL (Fin 2) A, Matrix.GeneralLinearGroup.scalar (Fin 2) a * k =
      k * Matrix.GeneralLinearGroup.scalar (Fin 2) a := fun k => by
    refine Units.ext ?_
    simp only [Matrix.GeneralLinearGroup.scalar, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, Matrix.scalar_apply]
    exact (Matrix.scalar_commute (a : A) (fun _ => Commute.all _ _) _).eq
  have h : ∀ k : GL (Fin 2) A, k⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) a * k =
      Matrix.GeneralLinearGroup.scalar (Fin 2) a := fun k => by
    rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]
  simp only [centralValue, h, integral_const]

end Slice

section Weights

variable {A : Type*} [CommRing A] (nrm : A → ℝ)

def ratio (a b : Aˣ) : ℝ :=
  nrm (1 - (b : A) * ((a⁻¹ : Aˣ) : A))

def sqrtRatio (a b : Aˣ) : ℝ :=
  Real.sqrt (nrm (a : A) / nrm (b : A))

theorem ratio_self (a : Aˣ) : ratio nrm a a = nrm 0 := by
  simp [ratio]

theorem sqrtRatio_self {a : Aˣ} (h : nrm (a : A) ≠ 0) : sqrtRatio nrm a a = 1 := by
  simp [sqrtRatio, div_self h]

end Weights

section Functionals

variable {A : Type*} [CommRing A] [MeasurableSpace (GL (Fin 2) A)] (μK : Measure (GL (Fin 2) A))
  [MeasurableSpace A] (μ : Measure A) (nrm : A → ℝ)

def splitOrbital (f : GL (Fin 2) A → ℂ) (a b : Aˣ) : ℂ :=
  ∫ x, slice μK f a b x ∂μ

@[simp] theorem splitOrbital_zero_fun (a b : Aˣ) : splitOrbital μK μ (fun _ => 0) a b = 0 := by
  simp [splitOrbital]

theorem splitOrbital_const_mul (c : ℂ) (f : GL (Fin 2) A → ℂ) (a b : Aˣ) :
    splitOrbital μK μ (fun g => c * f g) a b = c * splitOrbital μK μ f a b := by
  simp only [splitOrbital, slice_const_mul]
  exact integral_const_mul c _

def normSplitOrbital (f : GL (Fin 2) A → ℂ) (a b : Aˣ) : ℂ :=
  (sqrtRatio nrm a b : ℂ) * splitOrbital μK μ f a b

@[simp] theorem normSplitOrbital_zero_fun (a b : Aˣ) : normSplitOrbital μK μ nrm (fun _ => 0) a b = 0 := by
  simp [normSplitOrbital]

def halfWeighted (f : GL (Fin 2) A → ℂ) (a b : Aˣ) : ℂ :=
  -(sqrtRatio nrm a b : ℂ) *
    ∫ x in {x | ratio nrm a b < nrm x},
      slice μK f a b x * ((Real.log (nrm x) - Real.log (ratio nrm a b) : ℝ) : ℂ) ∂μ

@[simp] theorem halfWeighted_zero_fun (a b : Aˣ) : halfWeighted μK μ nrm (fun _ => 0) a b = 0 := by
  simp [halfWeighted]

def logMean : ℝ :=
  (∫ x in {x | nrm x ≤ 1}, Real.log (nrm x) ∂μ) / (μ {x | nrm x ≤ 1}).toReal

def bTerm (f : GL (Fin 2) A → ℂ) (a b : Aˣ) : ℂ :=
  if ratio nrm a b ≤ 1 then
    (sqrtRatio nrm a b : ℂ) * centralValue μK f a *
      ∫ x in {x | nrm x ≤ ratio nrm a b}, ((Real.log (nrm x) - Real.log (ratio nrm a b) : ℝ) : ℂ) ∂μ
  else 0

@[simp] theorem bTerm_zero_fun (a b : Aˣ) : bTerm μK μ nrm (fun _ => 0) a b = 0 := by
  simp [bTerm]

def cTerm (f : GL (Fin 2) A → ℂ) (a b : Aˣ) : ℂ :=
  if ratio nrm a b ≤ 1 then
    -(sqrtRatio nrm a b : ℂ) * (logMean μ nrm : ℂ) * splitOrbital μK μ f a a
  else 0

@[simp] theorem cTerm_zero_fun (a b : Aˣ) : cTerm μK μ nrm (fun _ => 0) a b = 0 := by
  simp [cTerm]

def invariantPart (f : GL (Fin 2) A → ℂ) (a b : Aˣ) : ℂ :=
  (Real.log (ratio nrm a b) : ℂ) * normSplitOrbital μK μ nrm f a b + bTerm μK μ nrm f a b + cTerm μK μ nrm f a b

@[simp] theorem invariantPart_zero_fun (a b : Aˣ) : invariantPart μK μ nrm (fun _ => 0) a b = 0 := by
  simp [invariantPart]

def correctionTerm (f : GL (Fin 2) A → ℂ) (a b : Aˣ) : ℂ :=
  halfWeighted μK μ nrm f a b - invariantPart μK μ nrm f a b

@[simp] theorem correctionTerm_zero_fun (a b : Aˣ) : correctionTerm μK μ nrm (fun _ => 0) a b = 0 := by
  simp [correctionTerm]

def unipotentMellin (f : GL (Fin 2) A → ℂ) (a : Aˣ) (s : ℂ) : ℂ :=
  ∫ x, slice μK f a a x * ((nrm x : ℝ) : ℂ) ^ s ∂μ

@[simp] theorem unipotentMellin_zero_fun (a : Aˣ) (s : ℂ) : unipotentMellin μK μ nrm (fun _ => 0) a s = 0 := by
  simp [unipotentMellin]

theorem halfWeighted_eq_add (f : GL (Fin 2) A → ℂ) (a b : Aˣ) :
    halfWeighted μK μ nrm f a b = invariantPart μK μ nrm f a b + correctionTerm μK μ nrm f a b := by
  rw [correctionTerm, add_sub_cancel]

theorem correctionTerm_self [Nontrivial A] (hn : ∀ x, 0 ≤ nrm x) (h0 : ∀ x, nrm x = 0 ↔ x = 0)
    (hμ : μ {0} = 0) (f : GL (Fin 2) A → ℂ) (a : Aˣ) :
    correctionTerm μK μ nrm f a a =
      -(∫ x, slice μK f a a x * (Real.log (nrm x) : ℂ) ∂μ) + (logMean μ nrm : ℂ) * splitOrbital μK μ f a a := by
  have h00 : nrm 0 = 0 := (h0 0).2 rfl
  have hr : ratio nrm a a = 0 := by rw [ratio_self, h00]
  have hs : sqrtRatio nrm a a = 1 := sqrtRatio_self nrm fun h => a.ne_zero ((h0 _).1 h)
  have hle : {x : A | nrm x ≤ 0} = {0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨fun h => (h0 x).1 (le_antisymm h (hn x)), fun h => h ▸ h00.le⟩
  have hlt : {x : A | 0 < nrm x} = {0}ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
    refine ⟨fun h hx => ?_, fun h => lt_of_le_of_ne (hn x) fun h' => h ((h0 x).1 h'.symm)⟩
    rw [hx, h00] at h
    exact lt_irrefl _ h
  have hb : bTerm μK μ nrm f a a = 0 := by
    simp only [bTerm, hr, zero_le_one, if_true, hle, Measure.restrict_eq_zero.2 hμ, integral_zero_measure,
      mul_zero]
  have hA1 : halfWeighted μK μ nrm f a a = -(∫ x, slice μK f a a x * (Real.log (nrm x) : ℂ) ∂μ) := by
    simp only [halfWeighted, hr, Real.log_zero, sub_zero, hs, Complex.ofReal_one, hlt]
    rw [Measure.restrict_congr_set (ae_eq_univ.2 (by rwa [compl_compl])), Measure.restrict_univ, neg_one_mul]
  have hc : cTerm μK μ nrm f a a = -((logMean μ nrm : ℂ) * splitOrbital μK μ f a a) := by
    simp only [cTerm, hr, zero_le_one, if_true, hs, Complex.ofReal_one]
    ring
  rw [correctionTerm, invariantPart, hA1, hb, hc, hr, Real.log_zero, Complex.ofReal_zero, zero_mul, zero_add,
    zero_add, sub_neg_eq_add]

end Functionals

section Inhabitant

example [MeasurableSpace ℚ] [MeasurableSpace (GL (Fin 2) ℚ)] (a b : ℚˣ) :
    correctionTerm (Measure.count : Measure (GL (Fin 2) ℚ)) (Measure.count : Measure ℚ) (fun _ => (0 : ℝ))
      (fun _ => (0 : ℂ)) a b = 0 :=
  correctionTerm_zero_fun _ _ _ a b

end Inhabitant

end LocalWeightedOrbital

end AutomorphicForm

end
