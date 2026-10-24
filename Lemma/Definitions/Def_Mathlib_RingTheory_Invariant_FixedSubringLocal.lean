import Mathlib

namespace FixedPoints

section Ring

variable {R : Type*} [Ring R] {M : Type*} [Monoid M] [MulSemiringAction M R]

theorem mem_subring_iff {x : R} :
    x ∈ FixedPoints.subring R M ↔ ∀ m : M, m • x = x :=
  Iff.rfl

theorem smul_eq_self_of_mul_eq_one {a b : R} (ha : a ∈ FixedPoints.subring R M)
    (hab : a * b = 1) (hba : b * a = 1) (m : M) : m • b = b := by
  have key : a * (m • b) = 1 := by
    have h : m • (a * b) = m • (1 : R) := congrArg (m • ·) hab
    rwa [smul_mul', mem_subring_iff.mp ha m, smul_one] at h
  exact (left_inv_eq_right_inv hba key).symm

theorem mem_subring_of_mul_eq_one {a b : R} (ha : a ∈ FixedPoints.subring R M)
    (hab : a * b = 1) (hba : b * a = 1) : b ∈ FixedPoints.subring R M :=
  mem_subring_iff.mpr fun m => smul_eq_self_of_mul_eq_one ha hab hba m

theorem isUnit_subring_iff (a : FixedPoints.subring R M) :
    IsUnit a ↔ IsUnit (a : R) := by
  constructor
  · intro h
    simpa using h.map (FixedPoints.subring R M).subtype
  · intro h
    obtain ⟨b, hab, hba⟩ := isUnit_iff_exists.mp h
    refine isUnit_iff_exists.mpr
      ⟨⟨b, mem_subring_of_mul_eq_one a.2 hab hba⟩, Subtype.ext ?_, Subtype.ext ?_⟩
    · simpa using hab
    · simpa using hba

instance isLocalHom_subring_subtype :
    IsLocalHom (FixedPoints.subring R M).subtype :=
  ⟨fun a h => (isUnit_subring_iff a).mpr (by simpa using h)⟩

instance isLocalRing_subring [IsLocalRing R] :
    IsLocalRing (FixedPoints.subring R M) :=
  ⟨fun {a b} hab => by
    have h : (a : R) + (b : R) = 1 := by
      have h1 : ((a + b : FixedPoints.subring R M) : R) = ((1 : FixedPoints.subring R M) : R) :=
        congrArg Subtype.val hab
      simpa using h1
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one h with h' | h'
    · exact Or.inl ((isUnit_subring_iff a).mpr h')
    · exact Or.inr ((isUnit_subring_iff b).mpr h')⟩

end Ring

theorem isLocalRing_subring_of_finite {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] :
    IsLocalRing (FixedPoints.subring R G) :=
  isLocalRing_subring

section MaximalIdeal

variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [Monoid M] [MulSemiringAction M R]

theorem mem_maximalIdeal_subring_iff {a : FixedPoints.subring R M} :
    a ∈ IsLocalRing.maximalIdeal (FixedPoints.subring R M) ↔
      (a : R) ∈ IsLocalRing.maximalIdeal R := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff]
  exact not_congr (isUnit_subring_iff a)

theorem maximalIdeal_subring_eq_comap :
    IsLocalRing.maximalIdeal (FixedPoints.subring R M) =
      Ideal.comap (FixedPoints.subring R M).subtype (IsLocalRing.maximalIdeal R) := by
  ext a
  rw [Ideal.mem_comap, Subring.subtype_apply]
  exact mem_maximalIdeal_subring_iff

theorem isMaximal_comap_maximalIdeal_subring :
    (Ideal.comap (FixedPoints.subring R M).subtype (IsLocalRing.maximalIdeal R)).IsMaximal := by
  rw [← maximalIdeal_subring_eq_comap (R := R) (M := M)]
  exact IsLocalRing.maximalIdeal.isMaximal _

end MaximalIdeal

section Degenerate

variable {R : Type*} [Ring R] {M : Type*} [Monoid M] [MulSemiringAction M R]

theorem subring_eq_top_of_forall_smul_eq (h : ∀ (m : M) (x : R), m • x = x) :
    FixedPoints.subring R M = ⊤ :=
  (Subring.eq_top_iff' _).mpr fun x => mem_subring_iff.mpr fun m => h m x

theorem subring_eq_top_of_subsingleton [Subsingleton M] :
    FixedPoints.subring R M = ⊤ :=
  subring_eq_top_of_forall_smul_eq fun m x => by
    rw [Subsingleton.elim m 1, one_smul]

def subringEquivOfSubsingleton [Subsingleton M] :
    FixedPoints.subring R M ≃+* R :=
  (RingEquiv.subringCongr (subring_eq_top_of_subsingleton (R := R) (M := M))).trans
    Subring.topEquiv

end Degenerate

end FixedPoints

section Gates

example {R : Type*} [CommRing R] [IsLocalRing R] {G : Type*} [Group G] [MulSemiringAction G R]
    (H : Subgroup G) : IsLocalRing (FixedPoints.subring R H) :=
  inferInstance

example {R : Type*} [CommRing R] [IsLocalRing R] {G : Type*} [Group G] [MulSemiringAction G R]
    (H : Subgroup G) [H.Normal] :
    IsLocalRing (FixedPoints.subring R H) ∧
      Nonempty (MulSemiringAction (G ⧸ H) (FixedPoints.subring R H)) :=
  ⟨inferInstance, ⟨inferInstance⟩⟩

example {R : Type*} [CommRing R] [IsLocalRing R] {G : Type*} [Group G] [Finite G]
    [MulSemiringAction G R] :
    IsLocalRing (FixedPoints.subring R G) ∧
      IsLocalRing.maximalIdeal (FixedPoints.subring R G) =
        Ideal.comap (Subring.subtype (FixedPoints.subring R G)) (IsLocalRing.maximalIdeal R) :=
  ⟨FixedPoints.isLocalRing_subring_of_finite, FixedPoints.maximalIdeal_subring_eq_comap⟩

example : IsLocalRing (FixedPoints.subring ℚ (ℚ →+* ℚ)) :=
  inferInstance

example : IsLocalHom (FixedPoints.subring ℚ (ℚ →+* ℚ)).subtype :=
  inferInstance

example {R : Type*} [CommRing R] (M : Type*) [Monoid M] :
    letI : MulSemiringAction M R := MulSemiringAction.compHom R (1 : M →* (R →+* R))
    FixedPoints.subring R M = ⊤ := by
  letI : MulSemiringAction M R := MulSemiringAction.compHom R (1 : M →* (R →+* R))
  exact FixedPoints.subring_eq_top_of_forall_smul_eq fun m x => rfl

example {R : Type*} [CommRing R] [IsLocalRing R] (M : Type*) [Monoid M] [Subsingleton M]
    [MulSemiringAction M R] :
    (FixedPoints.subring R M = ⊤) ∧
      Nonempty ((FixedPoints.subring R M) ≃+* R) ∧
      IsLocalRing (FixedPoints.subring R M) :=
  ⟨FixedPoints.subring_eq_top_of_subsingleton,
    ⟨FixedPoints.subringEquivOfSubsingleton⟩, inferInstance⟩

example {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [Monoid M]
    [MulSemiringAction M R] :
    (0 : FixedPoints.subring R M) ∈ IsLocalRing.maximalIdeal (FixedPoints.subring R M) ∧
      (1 : FixedPoints.subring R M) ∉ IsLocalRing.maximalIdeal (FixedPoints.subring R M) :=
  ⟨Ideal.zero_mem _,
    fun h => mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp h) isUnit_one⟩

example {R : Type*} [CommRing R] {M : Type*} [Monoid M] [MulSemiringAction M R]
    (a : FixedPoints.subring R M) (h : ¬ IsUnit (a : R)) : ¬ IsUnit a :=
  fun ha => h ((FixedPoints.isUnit_subring_iff a).mp ha)

end Gates

/-- info: 'FixedPoints.mem_subring_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms FixedPoints.mem_subring_iff

/-- info: 'FixedPoints.smul_eq_self_of_mul_eq_one' depends on axioms: [propext] -/
#guard_msgs in #print axioms FixedPoints.smul_eq_self_of_mul_eq_one

/-- info: 'FixedPoints.mem_subring_of_mul_eq_one' depends on axioms: [propext] -/
#guard_msgs in #print axioms FixedPoints.mem_subring_of_mul_eq_one

/-- info: 'FixedPoints.isUnit_subring_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms FixedPoints.isUnit_subring_iff

/-- info: 'FixedPoints.isLocalHom_subring_subtype' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms FixedPoints.isLocalHom_subring_subtype

/-- info: 'FixedPoints.isLocalRing_subring' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms FixedPoints.isLocalRing_subring

/-- info: 'FixedPoints.isLocalRing_subring_of_finite' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms FixedPoints.isLocalRing_subring_of_finite

/-- info: 'FixedPoints.mem_maximalIdeal_subring_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms FixedPoints.mem_maximalIdeal_subring_iff

/-- info: 'FixedPoints.maximalIdeal_subring_eq_comap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms FixedPoints.maximalIdeal_subring_eq_comap

/--
info: 'FixedPoints.isMaximal_comap_maximalIdeal_subring' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms FixedPoints.isMaximal_comap_maximalIdeal_subring

/--
info: 'FixedPoints.subring_eq_top_of_forall_smul_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms FixedPoints.subring_eq_top_of_forall_smul_eq

/--
info: 'FixedPoints.subring_eq_top_of_subsingleton' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms FixedPoints.subring_eq_top_of_subsingleton

/--
info: 'FixedPoints.subringEquivOfSubsingleton' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms FixedPoints.subringEquivOfSubsingleton
