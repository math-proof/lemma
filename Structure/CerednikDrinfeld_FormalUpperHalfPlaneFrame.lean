import Mathlib
import Structure.CerednikDrinfeld_FormalUpperHalfPlanePoints

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

namespace CerednikDrinfeld
namespace FormalOmega

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  {C : Type} [Field C] [Algebra K C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]

structure IsAdicFrame (π : 𝒪) (ϖ : PseudoUniformizer K C) (R : Type) [CommRing R] [Algebra 𝒪 R] [Algebra R C]
    [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K C] : Prop where

  irreducible : Irreducible π

  injective : Function.Injective (algebraMap R C)

  range_eq : ∀ c : C, Valued.v c ≤ 1 ↔ c ∈ Set.range (algebraMap R C)

  complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R

  integers : ∀ a : K, Valued.v (algebraMap K C a) ≤ 1 ↔ a ∈ Set.range (algebraMap 𝒪 K)

  isClosed_range : IsClosed (Set.range (algebraMap K C))

  unif : algebraMap 𝒪 C π = algebraMap K C ϖ.ϖ

end FormalOmega
end CerednikDrinfeld
