import Mathlib

open NumberField MeasureTheory Matrix

noncomputable section

namespace AutomorphicForm

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

abbrev AdelicGL2 : Type _ :=
  Matrix.GeneralLinearGroup (Fin 2) (AdeleRing R K)

def globalPoints : Matrix.GeneralLinearGroup (Fin 2) K →* AdelicGL2 R K :=
  Matrix.GeneralLinearGroup.map (algebraMap K (AdeleRing R K))

def centralScalar : (AdeleRing R K)ˣ →* AdelicGL2 R K :=
  Matrix.GeneralLinearGroup.scalar (Fin 2)

def IsIdeleClassChar (χ : (AdeleRing R K)ˣ →* ℂˣ) : Prop :=
  ∀ u : Kˣ, χ (Units.map (algebraMap K (AdeleRing R K)) u) = 1

def IsUnitaryChar (χ : (AdeleRing R K)ˣ →* ℂˣ) : Prop :=
  ∀ x : (AdeleRing R K)ˣ, ‖((χ x : ℂˣ) : ℂ)‖ = 1

def SquaresToXi (Z : Subgroup (AdeleRing R K)ˣ) (ξ : Z →* ℂˣ)
    (χ : (AdeleRing R K)ˣ →* ℂˣ) : Prop :=
  ∀ z : Z, χ (z : (AdeleRing R K)ˣ) ^ 2 = ξ z

variable (Z : Subgroup (AdeleRing R K)ˣ) (ξ : Z →* ℂˣ)

structure IsLsXiFunction (φ : AdelicGL2 R K → ℂ) : Prop where
  left_invariant : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 R K),
    φ (globalPoints R K γ * g) = φ g
  central_transform : ∀ (z : Z) (g : AdelicGL2 R K),
    φ (centralScalar R K (z : (AdeleRing R K)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * φ g

theorem isLsXiFunction_zero : IsLsXiFunction R K Z ξ (fun _ => (0 : ℂ)) :=
  ⟨fun _ _ => rfl, fun _ _ => by simp⟩

variable [MeasureSpace (AdelicGL2 R K)] (D : Set (AdelicGL2 R K))

structure LsXiMember (φ : AdelicGL2 R K → ℂ) : Prop extends IsLsXiFunction R K Z ξ φ where
  memLp_two : MemLp φ 2 ((volume : Measure (AdelicGL2 R K)).restrict D)

theorem lsXiMember_zero : LsXiMember R K Z ξ D (fun _ => (0 : ℂ)) :=
  ⟨isLsXiFunction_zero R K Z ξ, MemLp.zero'⟩

def chiDet (χ : (AdeleRing R K)ˣ →* ℂˣ) : AdelicGL2 R K → ℂ :=
  fun g => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)

end AutomorphicForm

end
