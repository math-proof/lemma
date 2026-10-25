import Mathlib
import Structure.AutomorphicForm_AdelicLsXi

open NumberField MeasureTheory Matrix

noncomputable section

namespace AutomorphicForm

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]


def IsIdeleClassChar (χ : (AdeleRing R K)ˣ →* ℂˣ) : Prop :=
  ∀ u : Kˣ, χ (Units.map (algebraMap K (AdeleRing R K)) u) = 1

def IsUnitaryChar (χ : (AdeleRing R K)ˣ →* ℂˣ) : Prop :=
  ∀ x : (AdeleRing R K)ˣ, ‖((χ x : ℂˣ) : ℂ)‖ = 1

def SquaresToXi (Z : Subgroup (AdeleRing R K)ˣ) (ξ : Z →* ℂˣ)
    (χ : (AdeleRing R K)ˣ →* ℂˣ) : Prop :=
  ∀ z : Z, χ (z : (AdeleRing R K)ˣ) ^ 2 = ξ z

variable (Z : Subgroup (AdeleRing R K)ˣ) (ξ : Z →* ℂˣ)


theorem isLsXiFunction_zero : IsLsXiFunction R K Z ξ (fun _ => (0 : ℂ)) :=
  ⟨fun _ _ => rfl, fun _ _ => by simp⟩

variable [MeasureSpace (AdelicGL2 R K)] (D : Set (AdelicGL2 R K))


theorem lsXiMember_zero : LsXiMember R K Z ξ D (fun _ => (0 : ℂ)) :=
  ⟨isLsXiFunction_zero R K Z ξ, MemLp.zero'⟩

def chiDet (χ : (AdeleRing R K)ˣ →* ℂˣ) : AdelicGL2 R K → ℂ :=
  fun g => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)

end AutomorphicForm

end
