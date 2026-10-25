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


variable (Z : Subgroup (AdeleRing R K)ˣ) (ξ : Z →* ℂˣ)

structure IsLsXiFunction (φ : AdelicGL2 R K → ℂ) : Prop where
  left_invariant : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 R K),
    φ (globalPoints R K γ * g) = φ g
  central_transform : ∀ (z : Z) (g : AdelicGL2 R K),
    φ (centralScalar R K (z : (AdeleRing R K)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * φ g


variable [MeasureSpace (AdelicGL2 R K)] (D : Set (AdelicGL2 R K))

structure LsXiMember (φ : AdelicGL2 R K → ℂ) : Prop extends IsLsXiFunction R K Z ξ φ where
  memLp_two : MemLp φ 2 ((volume : Measure (AdelicGL2 R K)).restrict D)


end AutomorphicForm

end
