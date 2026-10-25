import Def.AutomorphicForm_AdelicLsXi

noncomputable section

namespace AutomorphicForm

section EtaFamily

open NumberField

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]


def cpowChar (α : (AdeleRing R K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) :
    (AdeleRing R K)ˣ →* ℂˣ where
  toFun x := Units.mk0 ((((α x : ℝˣ) : ℝ) : ℂ) ^ s)
    (Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr (hα x).ne')))
  map_one' := by
    apply Units.ext
    show ((((α 1 : ℝˣ) : ℝ) : ℂ)) ^ s = 1
    rw [map_one, Units.val_one, Complex.ofReal_one, Complex.one_cpow]
  map_mul' x y := by
    apply Units.ext
    show ((((α (x * y) : ℝˣ) : ℝ) : ℂ)) ^ s
        = ((((α x : ℝˣ) : ℝ) : ℂ)) ^ s * ((((α y : ℝˣ) : ℝ) : ℂ)) ^ s
    rw [map_mul, Units.val_mul, Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg (hα x).le (hα y).le s


def IsPrincipalTrivial (α : (AdeleRing R K)ˣ →* ℝˣ) : Prop :=
  ∀ u : Kˣ, α (Units.map (algebraMap K (AdeleRing R K)) u) = 1


def etaFst (μ : (AdeleRing R K)ˣ →* ℂˣ) (α : (AdeleRing R K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) : (AdeleRing R K)ˣ →* ℂˣ :=
  μ * cpowChar α hα (s + 1 / 2)

def etaSnd (ν : (AdeleRing R K)ˣ →* ℂˣ) (α : (AdeleRing R K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) : (AdeleRing R K)ˣ →* ℂˣ :=
  ν * cpowChar α hα (-(s + 1 / 2))

end EtaFamily

end AutomorphicForm

end
