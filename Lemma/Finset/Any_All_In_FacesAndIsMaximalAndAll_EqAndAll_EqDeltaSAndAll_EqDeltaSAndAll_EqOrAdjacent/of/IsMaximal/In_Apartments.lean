import Mathlib
import sympy.Basic
import Structure.v1.Atlas.Buildings.code.Building.CombinatorialGeometry.ThreeChamber.Part2
import Lemma.Group.Atlas.v1.Buildings.code.Building.CombinatorialGeometry.ThreeChamber
open scoped Classical


namespace CombinatorialGeometry

/--
[auxiliary_retraction_exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CombinatorialGeometry/StrongIsoAuxiliary.lean)
-/
@[path]
lemma auxiliary_retraction_exists
  [DecidableEq V]
  {b : Building V}
  {δW : Building.WValuedDist b}
  {A : SimplicialComplex V}
  {C : Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (hC : A.IsMaximal C) :
-- imply
  ∃ (ρ : Finset V → Finset V), (∀ D, b.toChamberComplex.toSimplicialComplex.IsMaximal D → ρ D ∈ A.faces ∧ A.IsMaximal (ρ D)) ∧ (∀ D, D ∈ A.faces → A.IsMaximal D → ρ D = D) ∧ (∀ D, b.toChamberComplex.toSimplicialComplex.IsMaximal D → δW.delta C (ρ D) = δW.delta C D) ∧ (∀ D, b.toChamberComplex.toSimplicialComplex.IsMaximal D → δW.delta (ρ D) C = δW.delta D C) ∧ (∀ D₁ D₂, b.toChamberComplex.toSimplicialComplex.Adjacent D₁ D₂ → ρ D₁ = ρ D₂ ∨ A.Adjacent (ρ D₁) (ρ D₂)) :=
-- proof
  δW.delta_retraction_preserves A hA C hC

end CombinatorialGeometry

namespace CombinatorialGeometry

/--
[strong_isometry_determined_by_retraction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CombinatorialGeometry/StrongIsoAuxiliary.lean)
-/
@[path]
lemma strong_isometry_determined_by_retraction
  [DecidableEq V]
  {b : Building V}
  {δW : Building.WValuedDist b}
  {A : SimplicialComplex V}
  {C : Finset V}
  {ρ : Finset V → Finset V}
  {Y : Set (Finset V)}
  {f : Finset V → Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (hC : A.IsMaximal C)
  (hρ_max : ∀ D, b.toChamberComplex.toSimplicialComplex.IsMaximal D → ρ D ∈ A.faces ∧ A.IsMaximal (ρ D))
  (hρ_fix : ∀ D, D ∈ A.faces → A.IsMaximal D → ρ D = D)
  (hρ_delta : ∀ D, b.toChamberComplex.toSimplicialComplex.IsMaximal D → δW.delta C (ρ D) = δW.delta C D)
  (hY : ∀ y ∈ Y, b.toChamberComplex.toSimplicialComplex.IsMaximal y)
  (hf_img : ∀ y ∈ Y, f y ∈ A.faces)
  (hf_delta : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, δW.delta (f y₁) (f y₂) = δW.delta y₁ y₂) :
-- imply
  ∀ y ∈ Y, ρ y = f y :=
-- proof
  δW.delta_retraction_agrees_with_iso A hA C hC ρ hρ_max hρ_fix hρ_delta Y f hY hf_img hf_delta

end CombinatorialGeometry


-- created on 2026-10-23
