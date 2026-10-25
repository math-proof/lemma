import Mathlib
import Lemma.RingTheory.Valuation.LowerRamificationGroup

set_option autoImplicit false

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

section CompatibleHom

variable {H : Type*} [Group H] [MulSemiringAction H R]

theorem lowerRamificationGroup_comap_of_forall_smul_eq (f : H →* G)
    (hf : ∀ (h : H) (x : R), f h • x = h • x) (i : ℕ) :
    lowerRamificationGroup R H i = (lowerRamificationGroup R G i).comap f := by
  ext σ
  simp only [mem_lowerRamificationGroup, Subgroup.mem_comap, hf]

end CompatibleHom

section Subgroup

theorem mem_lowerRamificationGroup_subgroup {H : Subgroup G} {σ : H} {i : ℕ} :
    σ ∈ lowerRamificationGroup R H i ↔ (σ : G) ∈ lowerRamificationGroup R G i :=
  Iff.rfl

@[simp]
theorem lowerRamificationGroup_subgroupOf (H : Subgroup G) (i : ℕ) :
    (lowerRamificationGroup R G i).subgroupOf H = lowerRamificationGroup R H i :=
  rfl

@[simp]
theorem lowerRamificationGroup_map_subtype (H : Subgroup G) (i : ℕ) :
    (lowerRamificationGroup R H i).map H.subtype = lowerRamificationGroup R G i ⊓ H := by
  rw [← lowerRamificationGroup_subgroupOf H i, Subgroup.subgroupOf_map_subtype]

theorem lowerRamificationGroup_map_subtype' (H : Subgroup G) (i : ℕ) :
    (lowerRamificationGroup R H i).map H.subtype = H ⊓ lowerRamificationGroup R G i := by
  rw [lowerRamificationGroup_map_subtype, inf_comm]

theorem lowerRamificationGroup_subgroup_eq_top_iff (H : Subgroup G) (i : ℕ) :
    lowerRamificationGroup R H i = ⊤ ↔ H ≤ lowerRamificationGroup R G i := by
  rw [← lowerRamificationGroup_subgroupOf H i, Subgroup.subgroupOf_eq_top]

theorem lowerRamificationGroup_comap_inclusion {H K : Subgroup G} (hHK : H ≤ K) (i : ℕ) :
    lowerRamificationGroup R H i =
      (lowerRamificationGroup R K i).comap (Subgroup.inclusion hHK) :=
  lowerRamificationGroup_comap_of_forall_smul_eq (Subgroup.inclusion hHK) (fun _ _ => rfl) i

theorem lowerRamificationGroup_map_subtype_le_map_subtype {H K : Subgroup G} (hHK : H ≤ K)
    (i : ℕ) :
    (lowerRamificationGroup R H i).map H.subtype ≤
      (lowerRamificationGroup R K i).map K.subtype := by
  rw [lowerRamificationGroup_map_subtype, lowerRamificationGroup_map_subtype]
  exact inf_le_inf_left _ hHK

end Subgroup

end IsLocalRing

namespace ValuationSubring

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
variable {A : ValuationSubring L}

@[simp]
theorem lowerRamificationGroup_subgroupOf (H : Subgroup (A.decompositionSubgroup K)) (i : ℕ) :
    (A.lowerRamificationGroup K i).subgroupOf H = IsLocalRing.lowerRamificationGroup A H i :=
  rfl

theorem mem_lowerRamificationGroup_subgroup {H : Subgroup (A.decompositionSubgroup K)} {σ : H}
    {i : ℕ} :
    σ ∈ IsLocalRing.lowerRamificationGroup A H i ↔
      (σ : A.decompositionSubgroup K) ∈ A.lowerRamificationGroup K i :=
  Iff.rfl

@[simp]
theorem lowerRamificationGroup_map_subtype (H : Subgroup (A.decompositionSubgroup K)) (i : ℕ) :
    (IsLocalRing.lowerRamificationGroup A H i).map H.subtype =
      A.lowerRamificationGroup K i ⊓ H := by
  rw [← lowerRamificationGroup_subgroupOf H i, Subgroup.subgroupOf_map_subtype]

theorem lowerRamificationGroup_zero_map_subtype (H : Subgroup (A.decompositionSubgroup K)) :
    (IsLocalRing.lowerRamificationGroup A H 0).map H.subtype =
      A.inertiaSubgroup K ⊓ H := by
  rw [lowerRamificationGroup_map_subtype, lowerRamificationGroup_zero]

end ValuationSubring

section Gates

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

example (i : ℕ) :
    (IsLocalRing.lowerRamificationGroup R (⊤ : Subgroup G) i).map (⊤ : Subgroup G).subtype =
      IsLocalRing.lowerRamificationGroup R G i := by
  rw [IsLocalRing.lowerRamificationGroup_map_subtype, inf_top_eq]

example (i : ℕ) :
    IsLocalRing.lowerRamificationGroup R (⊥ : Subgroup G) i = ⊤ :=
  (IsLocalRing.lowerRamificationGroup_subgroup_eq_top_iff ⊥ i).mpr bot_le

example [Subsingleton G] (H : Subgroup G) (i : ℕ) :
    IsLocalRing.lowerRamificationGroup R H i = ⊤ := by
  refine (IsLocalRing.lowerRamificationGroup_subgroup_eq_top_iff H i).mpr fun σ _ => ?_
  rw [IsLocalRing.mem_lowerRamificationGroup]
  intro x
  rw [Subsingleton.elim σ 1, one_smul, sub_self]
  exact zero_mem _

example (H : Subgroup G) (i : ℕ) :
    (IsLocalRing.lowerRamificationGroup R H (i + 1)).map H.subtype ≤
      (IsLocalRing.lowerRamificationGroup R H i).map H.subtype := by
  rw [IsLocalRing.lowerRamificationGroup_map_subtype,
    IsLocalRing.lowerRamificationGroup_map_subtype]
  exact inf_le_inf_right _ (IsLocalRing.lowerRamificationGroup_antitone (by omega))

example {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
    (i : ℕ) :
    (IsLocalRing.lowerRamificationGroup A (⊤ : Subgroup (A.decompositionSubgroup K)) i).map
        (⊤ : Subgroup (A.decompositionSubgroup K)).subtype =
      A.lowerRamificationGroup K i := by
  rw [ValuationSubring.lowerRamificationGroup_map_subtype, inf_top_eq]

example {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
    (H : Subgroup (A.decompositionSubgroup K)) (i : ℕ) :
    (IsLocalRing.lowerRamificationGroup A H i).map H.subtype ≤ A.inertiaSubgroup K := by
  rw [ValuationSubring.lowerRamificationGroup_map_subtype]
  exact le_trans inf_le_left (ValuationSubring.lowerRamificationGroup_le_inertiaSubgroup i)

end Gates

/--
info: 'IsLocalRing.lowerRamificationGroup_comap_of_forall_smul_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.lowerRamificationGroup_comap_of_forall_smul_eq

/--
info: 'IsLocalRing.lowerRamificationGroup_subgroupOf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.lowerRamificationGroup_subgroupOf

/--
info: 'IsLocalRing.lowerRamificationGroup_map_subtype' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.lowerRamificationGroup_map_subtype

/--
info: 'IsLocalRing.lowerRamificationGroup_subgroup_eq_top_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.lowerRamificationGroup_subgroup_eq_top_iff

/--
info: 'IsLocalRing.lowerRamificationGroup_comap_inclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.lowerRamificationGroup_comap_inclusion

/--
info: 'ValuationSubring.lowerRamificationGroup_subgroupOf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms ValuationSubring.lowerRamificationGroup_subgroupOf

/--
info: 'ValuationSubring.lowerRamificationGroup_map_subtype' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms ValuationSubring.lowerRamificationGroup_map_subtype

/--
info: 'ValuationSubring.lowerRamificationGroup_zero_map_subtype' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms ValuationSubring.lowerRamificationGroup_zero_map_subtype
