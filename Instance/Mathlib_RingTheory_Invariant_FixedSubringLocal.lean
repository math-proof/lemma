-- Carved from Lemma/Definitions/Def_Mathlib_RingTheory_Invariant_FixedSubringLocal.lean: instance decls only.
import Mathlib

namespace FixedPoints

section Ring

variable {R : Type*} [Ring R] {M : Type*} [Monoid M] [MulSemiringAction M R]


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


end FixedPoints


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
