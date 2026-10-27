import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.Buildings.code.Building.PropositionRetractionProperties
open Set PropositionRetractionProperties


namespace PropositionRetractionProperties

/--
[boundedSubsets_iff_exists_orbit_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/PropositionRetractionProperties.lean)
-/
@[path]
lemma boundedSubsets_iff_exists_orbit_bounded
  [Group Gt]
  {M : CoxeterMatrix B_idx}
  {ctx : BuildingGroupContext Gt B_idx M}
  {E : Set Gt} :
-- imply
  ctx.born.isBounded E ↔ ∃ x : ctx.X, Bornology.IsBounded (orbitSet ctx.action E x) := by
-- proof
  constructor
  ·
    intro hE
    obtain ⟨x⟩ := ctx.nonempty
    exact ⟨x, (BoundedSubsetsEquivalence ctx E).1 hE x⟩
  ·
    intro ⟨x, hx⟩
    exact (BoundedSubsetsEquivalence ctx E).2.2
      (fun Y hY => (BoundedSubsetsEquivalence ctx E).2.1 ⟨x, hx⟩ Y hY)

end PropositionRetractionProperties

namespace PropositionRetractionProperties

/--
[boundedSubsets_iff_forall_action_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/PropositionRetractionProperties.lean)
-/
@[path]
lemma boundedSubsets_iff_forall_action_bounded
  [Group Gt]
  {M : CoxeterMatrix B_idx}
  {ctx : BuildingGroupContext Gt B_idx M}
  {E : Set Gt} :
-- imply
  ctx.born.isBounded E ↔ (∀ Y : Set ctx.X, Bornology.IsBounded Y → Bornology.IsBounded (actionOnSet ctx.action E Y)) := by
-- proof
  constructor
  ·
    intro hE Y hY
    have h12 := (BoundedSubsetsEquivalence ctx E).1 hE
    obtain ⟨x⟩ := ctx.nonempty
    exact (BoundedSubsetsEquivalence ctx E).2.1 ⟨x, h12 x⟩ Y hY
  ·
    exact (BoundedSubsetsEquivalence ctx E).2.2

end PropositionRetractionProperties

namespace PropositionRetractionProperties

/--
[exists_orbit_bounded_iff_forall_action_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/PropositionRetractionProperties.lean)
-/
@[path]
lemma exists_orbit_bounded_iff_forall_action_bounded
  [Group Gt]
  {M : CoxeterMatrix B_idx}
  {ctx : BuildingGroupContext Gt B_idx M}
  {E : Set Gt} :
-- imply
  (∃ x : ctx.X, Bornology.IsBounded (orbitSet ctx.action E x)) ↔ (∀ Y : Set ctx.X, Bornology.IsBounded Y → Bornology.IsBounded (actionOnSet ctx.action E Y)) := by
-- proof
  constructor
  ·
    exact (BoundedSubsetsEquivalence ctx E).2.1
  ·
    intro h_all
    obtain ⟨x₀⟩ := ctx.nonempty
    exact ⟨x₀, by rw [← actionOnSet_singleton]; exact h_all {x₀} Bornology.isBounded_singleton⟩

end PropositionRetractionProperties

namespace PropositionRetractionProperties

/--
[stabilizer_born_bounded_iff_orbit_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/PropositionRetractionProperties.lean)
-/
@[path]
lemma stabilizer_born_bounded_iff_orbit_bounded
  [Group Gt]
  {M : CoxeterMatrix B_idx}
  {ctx : BuildingGroupContext Gt B_idx M}
  {x : ctx.X} :
-- imply
  ctx.born.isBounded (pointStabilizer ctx.action x : Set Gt) ↔ Bornology.IsBounded (orbitSet ctx.action (pointStabilizer ctx.action x : Set Gt) x) := by
-- proof
  constructor
  · intro h
    exact born_bounded_orbit_bounded ctx _ h x
  · intro h
    exact orbit_bounded_born_bounded ctx _ ⟨x, h⟩

end PropositionRetractionProperties

namespace PropositionRetractionProperties

/--
[boundedSubsets_G_iff_orbit_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/PropositionRetractionProperties.lean)
-/
@[path]
lemma boundedSubsets_G_iff_orbit_bounded
  [Group Gt]
  {M : CoxeterMatrix B_idx}
  {ctx : BuildingGroupContext Gt B_idx M}
  {E : Set Gt}
-- given
  (hE_in_G : E ⊆ (ctx.gbnpair.G : Set Gt)) :
-- imply
  ctx.born.isBounded E ↔ ∃ x : ctx.X, Bornology.IsBounded (orbitSet ctx.action E x) :=
-- proof
  boundedSubsets_iff_exists_orbit_bounded ctx E

end PropositionRetractionProperties


-- created on 2026-10-23
