import Mathlib
import Instance.Mathlib_RingTheory_Valuation_LowerRamificationGroup

set_option autoImplicit false

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

variable (R G) in

noncomputable def lowerRamificationCard (i : ℕ) : ℕ :=
  Nat.card (lowerRamificationGroup R G i)


noncomputable def herbrandPhi (u : ℚ) : ℚ :=
  if u ≤ 0 then u
  else ((∑ i ∈ Finset.Icc 1 ⌊u⌋₊, (lowerRamificationCard R G i : ℚ)) +
      (u - ⌊u⌋₊) * lowerRamificationCard R G (⌊u⌋₊ + 1)) / lowerRamificationCard R G 0


noncomputable def herbrandPsi : ℚ → ℚ :=
  Function.invFun (herbrandPhi R G)


noncomputable def upperRamificationIndex (v : ℚ) : ℕ :=
  sInf {n : ℕ | v ≤ herbrandPhi R G n}

variable (R G) in

noncomputable def upperRamificationGroup (v : ℚ) : Subgroup G :=
  lowerRamificationGroup R G (upperRamificationIndex R G v)


def UpperRamificationQuotientCompat (S : Type*) [CommRing S] [IsLocalRing S]
    (H : Subgroup G) [H.Normal] [MulSemiringAction (G ⧸ H) S] : Prop :=
  ∀ v : ℚ, 0 ≤ v →
    (upperRamificationGroup R G v).map (QuotientGroup.mk' H) =
      upperRamificationGroup S (G ⧸ H) v

end IsLocalRing

namespace ValuationSubring

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]

noncomputable def herbrandPhi (A : ValuationSubring L) (u : ℚ) : ℚ :=
  IsLocalRing.herbrandPhi A (A.decompositionSubgroup K) u

noncomputable def herbrandPsi (A : ValuationSubring L) (v : ℚ) : ℚ :=
  IsLocalRing.herbrandPsi A (A.decompositionSubgroup K) v

noncomputable def upperRamificationGroup (A : ValuationSubring L) (v : ℚ) :
    Subgroup (A.decompositionSubgroup K) :=
  IsLocalRing.upperRamificationGroup A (A.decompositionSubgroup K) v

variable {K} {A : ValuationSubring L}


end ValuationSubring

section Gates

example {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] [Subsingleton G] {u : ℚ} (hu : 0 ≤ u) :
    IsLocalRing.herbrandPhi R G u = u := by
  rcases eq_or_lt_of_le hu with rfl | hu
  · simp
  · rw [IsLocalRing.herbrandPhi_of_pos hu]
    simp only [IsLocalRing.lowerRamificationCard_of_subsingleton, Nat.cast_one, mul_one,
      div_one]
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
    ring

example {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] [Subsingleton G] (v : ℚ) :
    IsLocalRing.upperRamificationGroup R G v = ⊤ := by
  ext σ
  simp [Subsingleton.elim σ 1]

example {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] [Finite G] :
    IsLocalRing.upperRamificationGroup R G 1 ≤ IsLocalRing.upperRamificationGroup R G 0 :=
  IsLocalRing.upperRamificationGroup_antitone (by norm_num)

example {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [MulSemiringAction G R]
    [MulSemiringAction (G ⧸ (⊤ : Subgroup G)) R] :
    IsLocalRing.UpperRamificationQuotientCompat R G R ⊤ := by
  intro v _
  haveI : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  ext x
  obtain rfl : x = 1 := Subsingleton.elim x 1
  exact iff_of_true (Subgroup.one_mem _) (Subgroup.one_mem _)

example {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] :
    MulSemiringAction (G ⧸ (⊤ : Subgroup G)) R :=
  MulSemiringAction.compHom R (1 : (G ⧸ (⊤ : Subgroup G)) →* RingAut R)

end Gates

/--
info: 'IsLocalRing.herbrandPhi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.herbrandPhi

/--
info: 'IsLocalRing.herbrandPhi_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.herbrandPhi_strictMono

/--
info: 'IsLocalRing.herbrandPsi_herbrandPhi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.herbrandPsi_herbrandPhi

/--
info: 'IsLocalRing.upperRamificationGroup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.upperRamificationGroup

/--
info: 'IsLocalRing.upperRamificationGroup_zero_eq_ker' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.upperRamificationGroup_zero_eq_ker

/--
info: 'IsLocalRing.upperRamificationGroup_antitone' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.upperRamificationGroup_antitone

/--
info: 'IsLocalRing.upperRamificationGroup_herbrandPhi_natCast' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.upperRamificationGroup_herbrandPhi_natCast

/--
info: 'IsLocalRing.UpperRamificationQuotientCompat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.UpperRamificationQuotientCompat

/--
info: 'ValuationSubring.upperRamificationGroup_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms ValuationSubring.upperRamificationGroup_zero
