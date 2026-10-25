import Mathlib
import Structure.AlgebraicGeometry_TwoAffineOpenCover
import Structure.AlgebraicGeometry_TwoChartCechLaurentChart
import Def.AlgebraicGeometry_TwoAffineOpenCoverSectional

set_option autoImplicit false

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

open CategoryTheory CategoryTheory.Limits Opposite

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))

structure IsSectional {ι : Type v} (σ : ι → (Spec (.of R) ⟶ X)) : Prop where

  comp_eq : ∀ i, σ i ≫ c = 𝟙 _

  range_subset : ∀ i, Set.range (σ i).base ⊆ (𝒱.U0 : Set X)

  compl_eq_iUnion : (𝒱.U1 : Set X)ᶜ = ⋃ i, Set.range (σ i).base

  pairwise_disjoint : Pairwise fun i j => Disjoint (Set.range (σ i).base) (Set.range (σ j).base)

variable {𝒱 c}


end AlgebraicGeometry.Scheme.TwoAffineOpenCover

end
