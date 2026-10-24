import Lemma.Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane

set_option autoImplicit false

open scoped MatrixGroups

namespace CerednikDrinfeld
namespace Omega

def IsDiscrete {K₀ : Type*} [Field K₀] (K : Type*) [Field K] [Algebra K₀ K]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) : Prop :=
  ∀ ε : Γ₀, ε ≠ 0 →
    {γ : G | ∃ g : GL (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g = ρ γ ∧
      (∀ i j : Fin 2, Valued.v (algebraMap K₀ K (g i j)) ≤ 1) ∧
      ε ≤ Valued.v (algebraMap K₀ K (Matrix.det (g : Matrix (Fin 2) (Fin 2) K₀)))}.Finite

end Omega
end CerednikDrinfeld
