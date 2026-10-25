import Mathlib
import Lemma.CerednikDrinfeld.FormalUpperHalfPlanePoints
import Structure.CerednikDrinfeld_FormalUpperHalfPlaneFrame

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

namespace CerednikDrinfeld
namespace FormalOmega

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  {C : Type} [Field C] [Algebra K C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]

namespace IsAdicFrame

variable {π : 𝒪} {ϖ : PseudoUniformizer K C} {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C]
  [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K C]

theorem v_algebraMap_lt_one (h : IsAdicFrame π ϖ R) : Valued.v (algebraMap 𝒪 C π) < 1 := by
  rw [h.unif]; exact ϖ.lt_one

theorem v_algebraMap_pos (h : IsAdicFrame π ϖ R) : 0 < Valued.v (algebraMap 𝒪 C π) := by
  rw [h.unif]; exact ϖ.pos

theorem v_algebraMap_le_one (h : IsAdicFrame π ϖ R) (r : R) : Valued.v (algebraMap R C r) ≤ 1 :=
  (h.range_eq _).mpr ⟨r, rfl⟩

end IsAdicFrame

end FormalOmega
end CerednikDrinfeld
