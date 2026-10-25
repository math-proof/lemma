import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.FieldTheory.Finite.GaloisField
import Instance.Compat_Mathlib430
import Instance.CuspidalType_IsCuspidalOfType

set_option autoImplicit false

open Polynomial

namespace CuspidalType

variable (q : ℕ) [Fact q.Prime]


def unipotent (t : ZMod q) : GL2 q :=
  ⟨!![1, t; 0, 1], !![1, -t; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def scalarElem : (ZMod q)ˣ →* GL2 q :=
  Units.map (Matrix.scalar (Fin 2) : ZMod q →+* Matrix (Fin 2) (Fin 2) (ZMod q)).toMonoidHom


variable (k : Type*) [Field k]


noncomputable def quadBasis : Module.Basis (Fin 2) (ZMod q) (GaloisField q 2) :=
  Module.finBasisOfFinrankEq (ZMod q) (GaloisField q 2) (GaloisField.finrank q two_ne_zero)

noncomputable def torus : (GaloisField q 2)ˣ →* GL2 q :=
  Units.map
    (MonoidHomClass.toMonoidHom
      ((LinearMap.toMatrixAlgEquiv (quadBasis q)).toAlgHom.comp
        (Algebra.lmul (ZMod q) (GaloisField q 2))))

variable {q} {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

structure IsCuspidalOfType (θ : (GaloisField q 2)ˣ →* Kˣ) (ρ : Representation K (GL2 q) V) : Prop where
  finrank_eq : Module.finrank K V = q - 1
  cuspidal : ∀ v : V, (∀ t : ZMod q, ρ (unipotent q t) v = v) → v = 0
  central : ∀ c : (ZMod q)ˣ, ρ (scalarElem q c) = LinearMap.id
  torus_charpoly : ∀ α : (GaloisField q 2)ˣ,
    LinearMap.charpoly (ρ (torus q α)) * ((X - C ((θ α : Kˣ) : K)) * (X - C (((θ α)⁻¹ : Kˣ) : K))) =
      LinearMap.charpoly (ind q K (torus q α))

end CuspidalType
