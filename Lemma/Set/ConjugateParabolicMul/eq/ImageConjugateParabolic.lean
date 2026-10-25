import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.BNPair.BuildingsFromBNPairs.Part6
open BNPair


namespace BNPair

/--
[conjugation_equivariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BuildingsFromBNPairs.lean)
-/
@[path]
lemma conjugation_equivariant
  [DecidableEq B_idx]
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {S' : Set B_idx}
-- given
  (g h : G) :
-- imply
  bp.conjugateParabolic (g * h) S' = (fun x => g * x * g⁻¹) '' bp.conjugateParabolic h S' := by
-- proof
  unfold conjugateParabolic
  ext y; simp only [Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨h * x * h⁻¹, ⟨x, hx, rfl⟩, by group⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by group⟩

end BNPair

namespace BNPair

/--
[leftCoset_left_action](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BuildingsFromBNPairs.lean)
-/
@[path]
lemma leftCoset_left_action
  [DecidableEq B_idx]
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {S' : Set B_idx}
-- given
  (g h : G) :
-- imply
  (fun x => g * x) '' bp.leftCoset h S' = bp.leftCoset (g * h) S' := by
-- proof
  unfold leftCoset
  ext y; simp only [Set.mem_image]
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by group⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨h * x, ⟨x, hx, rfl⟩, by group⟩

end BNPair

namespace BNPair

/--
[leftCoset_right_mul_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BuildingsFromBNPairs.lean)
-/
@[path]
lemma leftCoset_right_mul_eq
  [DecidableEq B_idx]
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {bd : BruhatProperties bp}
  {g : G}
  {S' : Set B_idx}
  {p : G}
-- given
  (hp : p ∈ bp.standardParabolic S') :
-- imply
  bp.leftCoset g S' = bp.leftCoset (g * p) S' := by
-- proof
  unfold leftCoset
  ext x; simp only [Set.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨p⁻¹ * q, (parabolicsAreSubgroups bp bd S').2.1 _ _
      ((parabolicsAreSubgroups bp bd S').2.2 _ hp) hq, ?_⟩
    group
  · rintro ⟨q, hq, rfl⟩
    refine ⟨p * q, (parabolicsAreSubgroups bp bd S').2.1 _ _ hp hq, ?_⟩
    group

end BNPair

namespace BNPair

/--
[bruhat_common_apartment](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BuildingsFromBNPairs.lean)
-/
@[path]
lemma bruhat_common_apartment
  [DecidableEq B_idx]
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {bd : BruhatProperties bp}
  {g₁ g₂ : G} :
-- imply
  ∃ (g : G), bp.leftCoset g₁ ∅ ∈ bp.translatedApartmentCosets g ∧ bp.leftCoset g₂ ∅ ∈ bp.translatedApartmentCosets g := by
-- proof
  obtain ⟨w, b₁, n, b₂, hπ, hg⟩ := bd.cell_cover (g₁⁻¹ * g₂)
  refine ⟨g₁ * b₁, ?_, ?_⟩
  ·
    refine ⟨⟨1, bp.N.one_mem⟩, ?_⟩
    rw [leftCoset_right_mul_eq bp bd g₁ (∅ : Set B_idx) b₁
      (B_mem_standardParabolic bp ∅ b₁ b₁.prop)]
    simp [leftCoset]
  ·
    refine ⟨n, ?_⟩
    have hg₂ : g₂ = g₁ * ((b₁ : G) * (n : G) * (b₂ : G)) := by
      rwa [inv_mul_eq_iff_eq_mul] at hg
    conv_lhs => rw [show g₂ = g₁ * (↑b₁ * ↑n) * ↑b₂ from by rw [hg₂]; group]
    rw [← leftCoset_right_mul_eq bp bd (g₁ * (↑b₁ * ↑n)) (∅ : Set B_idx) b₂
      (B_mem_standardParabolic bp ∅ b₂ b₂.prop)]
    congr 1; group

end BNPair

namespace BNPair

/--
[conjugation_preserves_order](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BuildingsFromBNPairs.lean)
-/
@[path]
lemma conjugation_preserves_order
  [DecidableEq B_idx]
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {bd : BruhatProperties bp}
  {ax : BNPairAxioms bp}
  {S₁ S₂ : Set B_idx}
-- given
  (g h : G) :
-- imply
  bp.leftCoset g S₁ ⊆ bp.leftCoset h S₂ ↔ bp.conjugateParabolic g S₁ ⊆ bp.conjugateParabolic h S₂ :=
-- proof
  ⟨conjugation_mono bp bd g h S₁ S₂,
    conjugation_reflects_order bp bd ax g h S₁ S₂⟩

end BNPair

namespace BNPair

/--
[conjugation_order_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BuildingsFromBNPairs.lean)
-/
@[path]
lemma conjugation_order_iff
  [DecidableEq B_idx]
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {bd : BruhatProperties bp}
  {ax : BNPairAxioms bp}
  {S₁ S₂ : Set B_idx}
-- given
  (g h : G) :
-- imply
  bp.leftCoset g S₁ ⊆ bp.leftCoset h S₂ ↔ bp.conjugateParabolic g S₁ ⊆ bp.conjugateParabolic h S₂ :=
-- proof
  conjugation_preserves_order bp bd ax g h S₁ S₂

end BNPair

namespace BNPair

/--
[poset_isomorphism_specialSubsets_properParabolics](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BuildingsFromBNPairs.lean)
-/
@[path]
lemma poset_isomorphism_specialSubsets_properParabolics
  [DecidableEq B_idx]
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {bd : BruhatProperties bp}
  {ax : BNPairAxioms bp} :
-- imply
  (∀ (g h : G) (S₁ S₂ : Set B_idx), bp.leftCoset g S₁ ⊆ bp.leftCoset h S₂ ↔ bp.conjugateParabolic g S₁ ⊆ bp.conjugateParabolic h S₂) ∧ (∀ (g h : G) (S' : Set B_idx), bp.leftCoset g S' = bp.leftCoset h S' → bp.conjugateParabolic g S' = bp.conjugateParabolic h S') ∧ (∀ (g h : G) (S₁ S₂ : Set B_idx), bp.conjugateParabolic g S₁ = bp.conjugateParabolic h S₂ → bp.leftCoset g S₁ = bp.leftCoset h S₂) ∧ (∀ Q ∈ bp.properParabolics, ∃ (g : G) (S' : Set B_idx), S' ≠ Set.univ ∧ Q = bp.conjugateParabolic g S') ∧ (∀ (g h : G) (S' : Set B_idx), bp.conjugateParabolic (g * h) S' = (fun x => g * x * g⁻¹) '' bp.conjugateParabolic h S') := by
-- proof
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    intro g h S₁ S₂
    exact conjugation_order_iff bp bd ax g h S₁ S₂
  ·
    intro g h S'
    exact conjugation_well_defined bp bd g h S'
  ·
    intro g h S₁ S₂
    exact conjugation_injective_on_cosets bp bd ax g h S₁ S₂
  ·
    intro Q hQ
    exact hQ
  ·
    intro g h S'
    exact conjugation_equivariant bp g h S'

end BNPair

namespace BNPair

/--
[specialSubsetRepr_ne_univ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BuildingsFromBNPairs.lean)
-/
@[path]
lemma specialSubsetRepr_ne_univ
  [DecidableEq B_idx]
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {X : bp.specialSubsets} :
-- imply
  bp.specialSubsetReprS X ≠ Set.univ :=
-- proof
  (specialSubsetRepr_prop bp X).1

end BNPair

namespace BNPair

/--
[properParabolicRepr_ne_univ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BuildingsFromBNPairs.lean)
-/
@[path]
lemma properParabolicRepr_ne_univ
  [DecidableEq B_idx]
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {Q : bp.properParabolics} :
-- imply
  bp.properParabolicReprS Q ≠ Set.univ :=
-- proof
  (properParabolicRepr_prop bp Q).1

end BNPair

/--
[coset_element_in_target](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BuildingsFromBNPairs.lean)
-/
@[path]
private lemma coset_element_in_target_eq
  [DecidableEq B_idx]
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {bd : BruhatProperties bp}
  {S₁ S₂ : Set B_idx}
-- given
  (g h : G)
  (hcontain : bp.leftCoset g S₁ ⊆ bp.leftCoset h S₂) :
-- imply
  ∃ q : G, q ∈ bp.standardParabolic S₂ ∧ g = h * q := by
-- proof
  apply BNPair.coset_element_in_target bp bd g h S₁ S₂ hcontain

/--
[coset_inclusion_implies_subgroup_inclusion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BuildingsFromBNPairs.lean)
-/
@[path]
private lemma coset_inclusion_implies_subgroup_inclusion_eq
  [DecidableEq B_idx]
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {bd : BruhatProperties bp}
  {S₁ S₂ : Set B_idx}
-- given
  (g h : G)
  (hcontain : bp.leftCoset g S₁ ⊆ bp.leftCoset h S₂) :
-- imply
  bp.standardParabolic S₁ ⊆ bp.standardParabolic S₂ := by
-- proof
  apply BNPair.coset_inclusion_implies_subgroup_inclusion bp bd g h S₁ S₂ hcontain

/--
[conjugation_well_defined](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BuildingsFromBNPairs.lean)
-/
@[path]
private lemma conjugation_well_defined_eq
  [DecidableEq B_idx]
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {bd : BruhatProperties bp}
  {S' : Set B_idx}
-- given
  (g h : G)
  (heq : bp.leftCoset g S' = bp.leftCoset h S') :
-- imply
  bp.conjugateParabolic g S' = bp.conjugateParabolic h S' := by
-- proof
  apply BNPair.conjugation_well_defined bp bd g h S' heq

/--
[conjugation_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BuildingsFromBNPairs.lean)
-/
@[path]
private lemma conjugation_mono_eq
  [DecidableEq B_idx]
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {bd : BruhatProperties bp}
  {S₁ S₂ : Set B_idx}
-- given
  (g h : G)
  (hcontain : bp.leftCoset g S₁ ⊆ bp.leftCoset h S₂) :
-- imply
  bp.conjugateParabolic g S₁ ⊆ bp.conjugateParabolic h S₂ := by
-- proof
  apply BNPair.conjugation_mono bp bd g h S₁ S₂ hcontain

/--
[labelling_well_defined](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BuildingsFromBNPairs.lean)
-/
@[path]
private lemma labelling_well_defined_eq
  [DecidableEq B_idx]
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {bd : BruhatProperties bp}
  {S₁ S₂ : Set B_idx}
-- given
  (g h : G)
  (heq : bp.leftCoset g S₁ = bp.leftCoset h S₂) :
-- imply
  S₁ = S₂ := by
-- proof
  apply BNPair.labelling_well_defined bp bd g h S₁ S₂ heq

/--
[B_mem_standardParabolic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BuildingsFromBNPairs.lean)
-/
@[path]
private lemma B_mem_standardParabolic_eq
  [DecidableEq B_idx]
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {S' : Set B_idx}
  {b : G}
-- given
  (hb : b ∈ bp.B) :
-- imply
  b ∈ bp.standardParabolic S' := by
-- proof
  apply BNPair.B_mem_standardParabolic bp S' b hb

/--
[conjugator_in_target_of_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BuildingsFromBNPairs.lean)
-/
@[path]
private lemma conjugator_in_target_of_subset_eq
  [DecidableEq B_idx]
  [Group G]
  {M : CoxeterMatrix B_idx}
  [DecidableEq B_idx]
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {bd : BruhatProperties bp}
  {ax : BNPairAxioms bp}
  {S₁ S₂ : Set B_idx}
  {g : G}
-- given
  (hsub : (fun x => g * x * g⁻¹) '' bp.standardParabolic S₁ ⊆ bp.standardParabolic S₂) :
-- imply
  g ∈ bp.standardParabolic S₂ := by
-- proof
  apply BNPair.conjugator_in_target_of_subset bp bd ax S₁ S₂ g hsub

/--
[subgroup_inclusion_of_conj_inclusion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BuildingsFromBNPairs.lean)
-/
@[path]
private lemma subgroup_inclusion_of_conj_inclusion_eq
  [DecidableEq B_idx]
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {bd : BruhatProperties bp}
  {ax : BNPairAxioms bp}
  {S₁ S₂ : Set B_idx}
  {g : G}
-- given
  (hsub : (fun x => g * x * g⁻¹) '' bp.standardParabolic S₁ ⊆ bp.standardParabolic S₂) :
-- imply
  bp.standardParabolic S₁ ⊆ bp.standardParabolic S₂ := by
-- proof
  apply BNPair.subgroup_inclusion_of_conj_inclusion bp bd ax S₁ S₂ g hsub

/--
[conjugation_reflects_order](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BuildingsFromBNPairs.lean)
-/
@[path]
private lemma conjugation_reflects_order_eq
  [DecidableEq B_idx]
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {bd : BruhatProperties bp}
  {ax : BNPairAxioms bp}
  {S₁ S₂ : Set B_idx}
-- given
  (g h : G)
  (hcontain : bp.conjugateParabolic g S₁ ⊆ bp.conjugateParabolic h S₂) :
-- imply
  bp.leftCoset g S₁ ⊆ bp.leftCoset h S₂ := by
-- proof
  apply BNPair.conjugation_reflects_order bp bd ax g h S₁ S₂ hcontain

/--
[conjugation_injective_on_cosets](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BuildingsFromBNPairs.lean)
-/
@[path]
private lemma conjugation_injective_on_cosets_eq
  [DecidableEq B_idx]
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {bd : BruhatProperties bp}
  {ax : BNPairAxioms bp}
  {S₁ S₂ : Set B_idx}
-- given
  (g h : G)
  (heq : bp.conjugateParabolic g S₁ = bp.conjugateParabolic h S₂) :
-- imply
  bp.leftCoset g S₁ = bp.leftCoset h S₂ := by
-- proof
  apply BNPair.conjugation_injective_on_cosets bp bd ax g h S₁ S₂ heq

/--
[specialSubsetRepr_prop](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BuildingsFromBNPairs.lean)
-/
@[path]
private lemma specialSubsetRepr_prop_eq
  [DecidableEq B_idx]
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {X : bp.specialSubsets} :
-- imply
  bp.specialSubsetReprS X ≠ Set.univ ∧ (X : Set G) = bp.leftCoset (bp.specialSubsetReprG X) (bp.specialSubsetReprS X) := by
-- proof
  apply BNPair.specialSubsetRepr_prop bp X

/--
[specialSubsetRepr_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BuildingsFromBNPairs.lean)
-/
@[path]
private lemma specialSubsetRepr_eq_eq
  [DecidableEq B_idx]
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {X : bp.specialSubsets} :
-- imply
  (X : Set G) = bp.leftCoset (bp.specialSubsetReprG X) (bp.specialSubsetReprS X) := by
-- proof
  apply BNPair.specialSubsetRepr_eq bp X

/--
[properParabolicRepr_prop](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BuildingsFromBNPairs.lean)
-/
@[path]
private lemma properParabolicRepr_prop_eq
  [DecidableEq B_idx]
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {Q : bp.properParabolics} :
-- imply
  bp.properParabolicReprS Q ≠ Set.univ ∧ (Q : Set G) = bp.conjugateParabolic (bp.properParabolicReprG Q) (bp.properParabolicReprS Q) := by
-- proof
  apply BNPair.properParabolicRepr_prop bp Q

/--
[properParabolicRepr_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BuildingsFromBNPairs.lean)
-/
@[path]
private lemma properParabolicRepr_eq_eq
  [DecidableEq B_idx]
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {Q : bp.properParabolics} :
-- imply
  (Q : Set G) = bp.conjugateParabolic (bp.properParabolicReprG Q) (bp.properParabolicReprS Q) := by
-- proof
  apply BNPair.properParabolicRepr_eq bp Q


-- created on 2026-10-23
