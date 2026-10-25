import Mathlib
import Instance.Mathlib_RingTheory_Valuation_LowerRamificationGroup

set_option autoImplicit false

open scoped Pointwise

open IsLocalRing

namespace Subgroup


end Subgroup

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]


end IsLocalRing

namespace IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]


noncomputable def ramificationDepth (σ : G) : ℕ∞ :=
  ⨅ x : R, addVal R (σ • x - x)


end IsDiscreteValuationRing

namespace ValuationSubring

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]

noncomputable def ramificationDepth (A : ValuationSubring L) [IsDiscreteValuationRing A]
    (σ : A.decompositionSubgroup K) : ℕ∞ :=
  IsDiscreteValuationRing.ramificationDepth A (A.decompositionSubgroup K) σ

variable {K} {A : ValuationSubring L} [IsDiscreteValuationRing A] {i : ℕ}


end ValuationSubring

section Gates

example {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] [Subsingleton G] (σ : G) :
    IsDiscreteValuationRing.ramificationDepth R G σ = ⊤ := by
  rw [Subsingleton.elim σ 1]
  exact IsDiscreteValuationRing.ramificationDepth_one

example {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] {σ : G} :
    σ ∈ IsLocalRing.lowerRamificationGroup R G 0 ↔
      (1 : ℕ∞) ≤ IsDiscreteValuationRing.ramificationDepth R G σ := by
  simpa using
    IsDiscreteValuationRing.mem_lowerRamificationGroup_iff_le_ramificationDepth
      (R := R) (G := G) (i := 0) (σ := σ)

example {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] [Subsingleton G] [FaithfulSMul G R] :
    ∃ N : ℕ, ∀ i, N ≤ i → IsLocalRing.lowerRamificationGroup R G i = ⊥ :=
  IsDiscreteValuationRing.exists_lowerRamificationGroup_eq_bot (R := R) (G := G)

example {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {x : R} :
    x ∈ IsLocalRing.maximalIdeal R ↔ (1 : ℕ∞) ≤ IsDiscreteValuationRing.addVal R x := by
  simpa using
    IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal (R := R) (n := 1) (x := x)

end Gates

/--
info: 'IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal

/--
info: 'IsDiscreteValuationRing.iInf_maximalIdeal_pow_eq_bot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsDiscreteValuationRing.iInf_maximalIdeal_pow_eq_bot

/--
info: 'IsDiscreteValuationRing.addVal_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsDiscreteValuationRing.addVal_smul

/--
info: 'IsDiscreteValuationRing.ramificationDepth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsDiscreteValuationRing.ramificationDepth

/--
info: 'IsDiscreteValuationRing.mem_lowerRamificationGroup_iff_le_ramificationDepth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms IsDiscreteValuationRing.mem_lowerRamificationGroup_iff_le_ramificationDepth

/--
info: 'IsDiscreteValuationRing.ramificationDepth_eq_top_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsDiscreteValuationRing.ramificationDepth_eq_top_iff

/--
info: 'Subgroup.exists_eq_bot_of_antitone_of_iInf_eq_bot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Subgroup.exists_eq_bot_of_antitone_of_iInf_eq_bot

/--
info: 'IsLocalRing.exists_lowerRamificationGroup_eq_bot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.exists_lowerRamificationGroup_eq_bot

/--
info: 'IsDiscreteValuationRing.exists_lowerRamificationGroup_eq_bot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms IsDiscreteValuationRing.exists_lowerRamificationGroup_eq_bot

/--
info: 'IsLocalRing.lowerRamificationGroup_finiteIndex' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.lowerRamificationGroup_finiteIndex

/--
info: 'IsLocalRing.isOpen_lowerRamificationGroup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.isOpen_lowerRamificationGroup

/--
info: 'ValuationSubring.mem_lowerRamificationGroup_iff_le_ramificationDepth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms ValuationSubring.mem_lowerRamificationGroup_iff_le_ramificationDepth

/--
info: 'ValuationSubring.exists_lowerRamificationGroup_eq_bot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms ValuationSubring.exists_lowerRamificationGroup_eq_bot
