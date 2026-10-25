import Mathlib
import sympy.Basic
import Structure.v1.Atlas.Buildings.code.BNPair.Basic.Part2
import Def.v1.Atlas.Buildings.code.BNPair.ParabolicDefs.Part2
import Lemma.Nat.NonemptyBruhatCell
import Lemma.Set.ConjugateParabolicMul.eq.ImageConjugateParabolic
import Def.v1.Atlas.Buildings.code.BNPair.BuildingsFromBNPairs.Part6


namespace BNPair

/--
[image_mul_left_comp'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BuildingAxiomsFromBNPairs.lean)
-/
@[path]
lemma image_mul_left_comp'
  [Group G]
  [DecidableEq B_idx]
  {M : CoxeterMatrix B_idx}
  {a b : G}
  {S : Set G} :
-- imply
  (fun x => a * x) '' ((fun x => b * x) '' S) = (fun x => a * b * x) '' S := by
-- proof
  ext x
  simp only [Set.mem_image]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by group⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨b * z, ⟨z, hz, rfl⟩, by group⟩

end BNPair

namespace BNPair

/--
[building_axiom_B2_cosets](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BuildingAxiomsFromBNPairs.lean)
-/
@[path]
lemma building_axiom_B2_cosets
  [Group G]
  [DecidableEq B_idx]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {bd : BruhatProperties bp}
  {ax : BNPairAxioms bp}
  {C : Set G}
-- given
  (g h : G)
  (hCg : C ∈ bp.translatedApartmentCosets g)
  (hCh : C ∈ bp.translatedApartmentCosets h) :
-- imply
  ∃ (t : G), (∀ X ∈ bp.translatedApartmentCosets g, (fun x => t * x) '' X ∈ bp.translatedApartmentCosets h) ∧ ((fun x => t * x) '' C = C) := by
-- proof
  obtain ⟨n₁, hCg'⟩ := hCg
  obtain ⟨n₂, hCh'⟩ := hCh
  refine ⟨h * ↑n₂ * (↑n₁)⁻¹ * g⁻¹, ?_, ?_⟩
  ·
    intro X hX
    obtain ⟨n, rfl⟩ := hX
    rw [leftCoset_left_action]
    have hcalc : h * ↑n₂ * (↑n₁)⁻¹ * g⁻¹ * (g * ↑n) = h * (↑n₂ * (↑n₁)⁻¹ * ↑n) := by group
    rw [hcalc]
    exact ⟨⟨↑n₂ * (↑n₁)⁻¹ * ↑n,
      bp.N.mul_mem (bp.N.mul_mem n₂.2 (bp.N.inv_mem n₁.2)) n.2⟩, rfl⟩
  ·
    rw [hCg', leftCoset_left_action]
    have hcalc : h * ↑n₂ * (↑n₁)⁻¹ * g⁻¹ * (g * ↑n₁) = h * ↑n₂ := by group
    rw [hcalc]
    exact hCh'.symm.trans hCg'

end BNPair


-- created on 2026-10-23
