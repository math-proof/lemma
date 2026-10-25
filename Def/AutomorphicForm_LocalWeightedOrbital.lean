import Lemma.AutomorphicForm.LocalOrbitalBase
import Def.AutomorphicForm_ConstantTerm
import Def.LanglandsTunnell_CubicInduction_TorusValues

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

end Algebra

section Slice

variable {A : Type*} [CommRing A] [MeasurableSpace (GL (Fin 2) A)] (μK : Measure (GL (Fin 2) A))

def slice (f : GL (Fin 2) A → ℂ) (a b : Aˣ) (x : A) : ℂ :=
  ∫ k, f (arg k a b x) ∂μK


def centralValue (f : GL (Fin 2) A → ℂ) (a : Aˣ) : ℂ :=
  ∫ k, f (k⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) a * k) ∂μK

end Slice

section Weights

variable {A : Type*} [CommRing A] (nrm : A → ℝ)

def ratio (a b : Aˣ) : ℝ :=
  nrm (1 - (b : A) * ((a⁻¹ : Aˣ) : A))

def sqrtRatio (a b : Aˣ) : ℝ :=
  Real.sqrt (nrm (a : A) / nrm (b : A))

end Weights

section Functionals

variable {A : Type*} [CommRing A] [MeasurableSpace (GL (Fin 2) A)] (μK : Measure (GL (Fin 2) A))
  [MeasurableSpace A] (μ : Measure A) (nrm : A → ℝ)

def splitOrbital (f : GL (Fin 2) A → ℂ) (a b : Aˣ) : ℂ :=
  ∫ x, slice μK f a b x ∂μ


def normSplitOrbital (f : GL (Fin 2) A → ℂ) (a b : Aˣ) : ℂ :=
  (sqrtRatio nrm a b : ℂ) * splitOrbital μK μ f a b


def halfWeighted (f : GL (Fin 2) A → ℂ) (a b : Aˣ) : ℂ :=
  -(sqrtRatio nrm a b : ℂ) *
    ∫ x in {x | ratio nrm a b < nrm x},
      slice μK f a b x * ((Real.log (nrm x) - Real.log (ratio nrm a b) : ℝ) : ℂ) ∂μ


def logMean : ℝ :=
  (∫ x in {x | nrm x ≤ 1}, Real.log (nrm x) ∂μ) / (μ {x | nrm x ≤ 1}).toReal

def bTerm (f : GL (Fin 2) A → ℂ) (a b : Aˣ) : ℂ :=
  if ratio nrm a b ≤ 1 then
    (sqrtRatio nrm a b : ℂ) * centralValue μK f a *
      ∫ x in {x | nrm x ≤ ratio nrm a b}, ((Real.log (nrm x) - Real.log (ratio nrm a b) : ℝ) : ℂ) ∂μ
  else 0


def cTerm (f : GL (Fin 2) A → ℂ) (a b : Aˣ) : ℂ :=
  if ratio nrm a b ≤ 1 then
    -(sqrtRatio nrm a b : ℂ) * (logMean μ nrm : ℂ) * splitOrbital μK μ f a a
  else 0


def invariantPart (f : GL (Fin 2) A → ℂ) (a b : Aˣ) : ℂ :=
  (Real.log (ratio nrm a b) : ℂ) * normSplitOrbital μK μ nrm f a b + bTerm μK μ nrm f a b + cTerm μK μ nrm f a b


def correctionTerm (f : GL (Fin 2) A → ℂ) (a b : Aˣ) : ℂ :=
  halfWeighted μK μ nrm f a b - invariantPart μK μ nrm f a b


def unipotentMellin (f : GL (Fin 2) A → ℂ) (a : Aˣ) (s : ℂ) : ℂ :=
  ∫ x, slice μK f a a x * ((nrm x : ℝ) : ℂ) ^ s ∂μ

end Functionals

end LocalWeightedOrbital

end AutomorphicForm

end
