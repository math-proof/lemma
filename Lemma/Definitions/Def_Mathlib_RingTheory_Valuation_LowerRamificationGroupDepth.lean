import Mathlib
import Lemma.Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup

set_option autoImplicit false

open scoped Pointwise

open IsLocalRing

namespace Subgroup

theorem exists_eq_bot_of_antitone_of_iInf_eq_bot {H : Type*} [Group H] [Finite H]
    {f : ℕ → Subgroup H} (hf : Antitone f) (hbot : ⨅ i, f i = ⊥) :
    ∃ N : ℕ, ∀ i, N ≤ i → f i = ⊥ := by
  classical
  cases nonempty_fintype H

  have key : ∀ g : H, ∃ n : ℕ, g ∈ f n → g = 1 := by
    intro g
    by_cases hg : g = 1
    · exact ⟨0, fun _ => hg⟩
    · have hnot : g ∉ ⨅ i, f i := by
        rw [hbot]
        simpa [Subgroup.mem_bot] using hg
      simp only [Subgroup.mem_iInf, not_forall] at hnot
      obtain ⟨n, hn⟩ := hnot
      exact ⟨n, fun h => absurd h hn⟩
  choose level hlevel using key
  refine ⟨Finset.univ.sup level, fun i hi => ?_⟩
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  exact hlevel g (hf (le_trans (Finset.le_sup (Finset.mem_univ g)) hi) hg)

end Subgroup

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

theorem smul_mem_maximalIdeal_pow_iff {σ : G} {n : ℕ} {x : R} :
    σ • x ∈ (maximalIdeal R) ^ n ↔ x ∈ (maximalIdeal R) ^ n := by
  have h := Ideal.smul_mem_pointwise_smul_iff (a := σ) (S := (maximalIdeal R) ^ n) (x := x)
  rwa [pointwise_smul_maximalIdeal_pow] at h

theorem exists_lowerRamificationGroup_eq_bot [Finite G] [FaithfulSMul G R]
    (hsep : ⨅ n, (maximalIdeal R) ^ n = ⊥) :
    ∃ N : ℕ, ∀ i, N ≤ i → lowerRamificationGroup R G i = ⊥ :=
  Subgroup.exists_eq_bot_of_antitone_of_iInf_eq_bot lowerRamificationGroup_antitone
    (iInf_lowerRamificationGroup_eq_bot hsep)

theorem lowerRamificationGroup_finiteIndex [Finite G] (i : ℕ) :
    (lowerRamificationGroup R G i).FiniteIndex :=
  Subgroup.finiteIndex_of_finite

theorem isOpen_lowerRamificationGroup [TopologicalSpace G] [DiscreteTopology G] (i : ℕ) :
    IsOpen ((lowerRamificationGroup R G i : Subgroup G) : Set G) :=
  isOpen_discrete _

end IsLocalRing

namespace IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

theorem mem_maximalIdeal_pow_iff_le_addVal {n : ℕ} {x : R} :
    x ∈ (IsLocalRing.maximalIdeal R) ^ n ↔ (n : ℕ∞) ≤ addVal R x := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← addVal_le_iff_dvd, hϖ.addVal_pow]

theorem iInf_maximalIdeal_pow_eq_bot :
    ⨅ n : ℕ, (IsLocalRing.maximalIdeal R) ^ n = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Ideal.mem_iInf] at hx
  rw [Ideal.mem_bot, ← addVal_eq_top_iff (R := R), ENat.eq_top_iff_forall_ge]
  intro m
  exact mem_maximalIdeal_pow_iff_le_addVal.mp (hx m)

theorem addVal_smul (σ : G) (x : R) : addVal R (σ • x) = addVal R x := by
  refine eq_of_forall_le_iff fun c => ?_
  induction c with
  | top => simp only [top_le_iff, addVal_eq_top_iff, smul_eq_zero_iff_eq]
  | coe n =>
    rw [← mem_maximalIdeal_pow_iff_le_addVal, ← mem_maximalIdeal_pow_iff_le_addVal,
      IsLocalRing.smul_mem_maximalIdeal_pow_iff]

variable (R G) in

noncomputable def ramificationDepth (σ : G) : ℕ∞ :=
  ⨅ x : R, addVal R (σ • x - x)

theorem ramificationDepth_def (σ : G) :
    ramificationDepth R G σ = ⨅ x : R, addVal R (σ • x - x) :=
  rfl

theorem le_ramificationDepth_iff {n : ℕ} {σ : G} :
    (n : ℕ∞) ≤ ramificationDepth R G σ ↔
      ∀ x : R, σ • x - x ∈ (IsLocalRing.maximalIdeal R) ^ n := by
  rw [ramificationDepth_def, le_iInf_iff]
  exact forall_congr' fun x => mem_maximalIdeal_pow_iff_le_addVal.symm

theorem mem_lowerRamificationGroup_iff_le_ramificationDepth {i : ℕ} {σ : G} :
    σ ∈ IsLocalRing.lowerRamificationGroup R G i ↔
      (i : ℕ∞) + 1 ≤ ramificationDepth R G σ := by
  rw [← Nat.cast_add_one, le_ramificationDepth_iff]
  exact IsLocalRing.mem_lowerRamificationGroup

theorem setOf_add_one_le_ramificationDepth_eq (i : ℕ) :
    {σ : G | (i : ℕ∞) + 1 ≤ ramificationDepth R G σ} =
      (IsLocalRing.lowerRamificationGroup R G i : Set G) := by
  ext σ
  simp only [Set.mem_setOf_eq, SetLike.mem_coe,
    mem_lowerRamificationGroup_iff_le_ramificationDepth]

theorem ramificationDepth_one : ramificationDepth R G (1 : G) = ⊤ := by
  rw [ramificationDepth_def]
  simp only [one_smul, sub_self, addVal_zero, iInf_top]

theorem ramificationDepth_eq_top_iff [FaithfulSMul G R] {σ : G} :
    ramificationDepth R G σ = ⊤ ↔ σ = 1 := by
  constructor
  · intro h
    refine FaithfulSMul.eq_of_smul_eq_smul (α := R) fun x => ?_
    have hle : ramificationDepth R G σ ≤ addVal R (σ • x - x) := by
      rw [ramificationDepth_def]
      exact iInf_le _ x
    rw [h, top_le_iff] at hle
    have hx : σ • x - x = 0 := addVal_eq_top_iff.mp hle
    rw [sub_eq_zero] at hx
    exact hx.trans (one_smul G x).symm
  · rintro rfl
    exact ramificationDepth_one

theorem exists_lowerRamificationGroup_eq_bot [Finite G] [FaithfulSMul G R] :
    ∃ N : ℕ, ∀ i, N ≤ i → IsLocalRing.lowerRamificationGroup R G i = ⊥ :=
  IsLocalRing.exists_lowerRamificationGroup_eq_bot iInf_maximalIdeal_pow_eq_bot

theorem isOpen_setOf_le_ramificationDepth [TopologicalSpace G] [DiscreteTopology G] (n : ℕ) :
    IsOpen {σ : G | (n : ℕ∞) ≤ ramificationDepth R G σ} :=
  isOpen_discrete _

end IsDiscreteValuationRing

namespace ValuationSubring

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]

noncomputable def ramificationDepth (A : ValuationSubring L) [IsDiscreteValuationRing A]
    (σ : A.decompositionSubgroup K) : ℕ∞ :=
  IsDiscreteValuationRing.ramificationDepth A (A.decompositionSubgroup K) σ

variable {K} {A : ValuationSubring L} [IsDiscreteValuationRing A] {i : ℕ}

theorem mem_lowerRamificationGroup_iff_le_ramificationDepth {σ : A.decompositionSubgroup K} :
    σ ∈ A.lowerRamificationGroup K i ↔ (i : ℕ∞) + 1 ≤ A.ramificationDepth K σ :=
  IsDiscreteValuationRing.mem_lowerRamificationGroup_iff_le_ramificationDepth

theorem exists_lowerRamificationGroup_eq_bot [Finite (A.decompositionSubgroup K)]
    [FaithfulSMul (A.decompositionSubgroup K) A] :
    ∃ N : ℕ, ∀ i, N ≤ i → A.lowerRamificationGroup K i = ⊥ :=
  IsDiscreteValuationRing.exists_lowerRamificationGroup_eq_bot

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
