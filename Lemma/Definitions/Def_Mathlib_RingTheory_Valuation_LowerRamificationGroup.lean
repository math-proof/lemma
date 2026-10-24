import Mathlib

set_option autoImplicit false

open scoped Pointwise

namespace Ideal

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [MulSemiringAction G R]

theorem inertia_mono {I J : Ideal R} (h : I ≤ J) :
    I.inertia G ≤ J.inertia G :=
  AddSubgroup.inertia_mono G (Submodule.toAddSubgroup_mono h)

@[simp]
theorem inertia_top : (⊤ : Ideal R).inertia G = ⊤ := by
  ext; simp [Ideal.inertia, AddSubgroup.inertia]

theorem inertia_normal_of_forall_smul_eq {I : Ideal R}
    (hI : ∀ g : G, g • I = I) : (I.inertia G).Normal := by
  refine ⟨fun σ hσ τ x => ?_⟩

  have key : τ • (σ • (τ⁻¹ • x) - τ⁻¹ • x) ∈ τ • I :=
    Ideal.smul_mem_pointwise_smul _ _ _ (hσ _)
  simpa [smul_sub, smul_smul, mul_assoc, hI τ] using key

end Ideal

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

@[simp]
theorem pointwise_smul_maximalIdeal (g : G) :
    g • maximalIdeal R = maximalIdeal R := by
  refine le_antisymm (le_maximalIdeal_of_isPrime _) ?_
  rw [Ideal.subset_pointwise_smul_iff]
  exact le_maximalIdeal_of_isPrime _

@[simp]
theorem pointwise_smul_maximalIdeal_pow (g : G) (n : ℕ) :
    g • (maximalIdeal R) ^ n = (maximalIdeal R) ^ n := by
  rw [Ideal.pointwise_smul_def, Ideal.map_pow, ← Ideal.pointwise_smul_def,
    pointwise_smul_maximalIdeal]

variable (R G) in

def lowerRamificationGroup (i : ℕ) : Subgroup G :=
  ((maximalIdeal R) ^ (i + 1)).inertia G

variable {i : ℕ}

@[simp]
theorem mem_lowerRamificationGroup {σ : G} :
    σ ∈ lowerRamificationGroup R G i ↔ ∀ x : R, σ • x - x ∈ (maximalIdeal R) ^ (i + 1) :=
  Iff.rfl

theorem lowerRamificationGroup_antitone :
    Antitone (lowerRamificationGroup R G) := fun _ _ hij =>
  Ideal.inertia_mono (Ideal.pow_le_pow_right (by omega))

instance lowerRamificationGroup_normal (i : ℕ) :
    (lowerRamificationGroup R G i).Normal :=
  Ideal.inertia_normal_of_forall_smul_eq fun g => pointwise_smul_maximalIdeal_pow g (i + 1)

theorem lowerRamificationGroup_zero_eq_ker :
    lowerRamificationGroup R G 0 =
      MonoidHom.ker (MulSemiringAction.toRingAut G (ResidueField R)) := by
  ext σ
  simp only [mem_lowerRamificationGroup, zero_add, pow_one, MonoidHom.mem_ker]
  constructor
  · intro hσ
    ext y
    obtain ⟨r, rfl⟩ := residue_surjective y
    have : residue R (σ • r - r) = 0 := (residue_eq_zero_iff _).mpr (hσ r)
    simpa [sub_eq_zero, ResidueField.residue_smul] using this
  · intro hσ r
    rw [← residue_eq_zero_iff, map_sub, ResidueField.residue_smul, sub_eq_zero]
    exact DFunLike.congr_fun hσ (residue R r)

theorem lowerRamificationGroup_zero_eq_inertia :
    lowerRamificationGroup R G 0 = (maximalIdeal R).inertia G := by
  simp only [lowerRamificationGroup, zero_add, pow_one]

theorem lowerRamificationGroup_le_zero (i : ℕ) :
    lowerRamificationGroup R G i ≤ lowerRamificationGroup R G 0 :=
  lowerRamificationGroup_antitone (Nat.zero_le i)

theorem iInf_lowerRamificationGroup_le_ker_toRingAut
    (hsep : ⨅ n, (maximalIdeal R) ^ n = ⊥) :
    ⨅ i, lowerRamificationGroup R G i ≤
      MonoidHom.ker (MulSemiringAction.toRingAut G R) := by
  intro σ hσ
  simp only [Subgroup.mem_iInf, mem_lowerRamificationGroup] at hσ
  ext x
  have : σ • x - x ∈ ⨅ n, (maximalIdeal R) ^ n := by
    simp only [Ideal.mem_iInf]
    intro n
    rcases n with _ | n
    · simp
    · exact hσ n x
  rw [hsep] at this
  simpa [sub_eq_zero] using this

theorem iInf_lowerRamificationGroup_eq_bot
    (hsep : ⨅ n, (maximalIdeal R) ^ n = ⊥) [FaithfulSMul G R] :
    ⨅ i, lowerRamificationGroup R G i = (⊥ : Subgroup G) := by
  refine le_bot_iff.mp fun σ hσ => ?_
  have h := iInf_lowerRamificationGroup_le_ker_toRingAut hsep hσ
  rw [MonoidHom.mem_ker] at h
  exact FaithfulSMul.eq_of_smul_eq_smul (α := R) fun x => by
    have := DFunLike.congr_fun h x; simpa using this.trans (one_smul G x).symm

end IsLocalRing

namespace ValuationSubring

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]

def lowerRamificationGroup (A : ValuationSubring L) (i : ℕ) :
    Subgroup (A.decompositionSubgroup K) :=
  IsLocalRing.lowerRamificationGroup A (A.decompositionSubgroup K) i

variable {K} {A : ValuationSubring L} {i : ℕ}

@[simp]
theorem mem_lowerRamificationGroup {σ : A.decompositionSubgroup K} :
    σ ∈ A.lowerRamificationGroup K i ↔
      ∀ a : A, σ • a - a ∈ (IsLocalRing.maximalIdeal A) ^ (i + 1) :=
  Iff.rfl

theorem lowerRamificationGroup_antitone :
    Antitone (A.lowerRamificationGroup K) :=
  IsLocalRing.lowerRamificationGroup_antitone

instance lowerRamificationGroup_normal (i : ℕ) :
    (A.lowerRamificationGroup K i).Normal :=
  IsLocalRing.lowerRamificationGroup_normal i

theorem lowerRamificationGroup_zero :
    A.lowerRamificationGroup K 0 = A.inertiaSubgroup K :=
  IsLocalRing.lowerRamificationGroup_zero_eq_ker

theorem lowerRamificationGroup_le_inertiaSubgroup (i : ℕ) :
    A.lowerRamificationGroup K i ≤ A.inertiaSubgroup K :=
  lowerRamificationGroup_zero (K := K) (A := A) ▸ IsLocalRing.lowerRamificationGroup_le_zero i

end ValuationSubring

section Gates

example {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] [Subsingleton G] (i : ℕ) :
    IsLocalRing.lowerRamificationGroup R G i = ⊤ := by
  ext σ; simp [Subsingleton.elim σ 1]

example {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] :
    IsLocalRing.lowerRamificationGroup R G 1 ≤
      IsLocalRing.lowerRamificationGroup R G 0 :=
  IsLocalRing.lowerRamificationGroup_antitone (by omega)

example {R : Type*} [CommRing R] [IsLocalRing R] {G : Type*} [Group G] [MulSemiringAction G R] :
    (IsLocalRing.lowerRamificationGroup R G 0 : Set G) =
      ((IsLocalRing.maximalIdeal R).inertia G : Set G) := by
  rw [IsLocalRing.lowerRamificationGroup_zero_eq_inertia]

end Gates

/--
info: 'IsLocalRing.lowerRamificationGroup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.lowerRamificationGroup

/--
info: 'IsLocalRing.lowerRamificationGroup_antitone' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.lowerRamificationGroup_antitone

/--
info: 'IsLocalRing.lowerRamificationGroup_normal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.lowerRamificationGroup_normal

/--
info: 'IsLocalRing.lowerRamificationGroup_zero_eq_ker' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.lowerRamificationGroup_zero_eq_ker

/--
info: 'IsLocalRing.iInf_lowerRamificationGroup_eq_bot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.iInf_lowerRamificationGroup_eq_bot

/--
info: 'ValuationSubring.lowerRamificationGroup_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms ValuationSubring.lowerRamificationGroup_zero

/--
info: 'ValuationSubring.lowerRamificationGroup_le_inertiaSubgroup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms ValuationSubring.lowerRamificationGroup_le_inertiaSubgroup
