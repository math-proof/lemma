-- Carved from Lemma/Definitions/Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup.lean: instance decls only.
import Mathlib
import Lemma.RingTheory.Valuation.LowerRamificationGroup

set_option autoImplicit false

open scoped Pointwise


namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

variable {i : ℕ}

instance lowerRamificationGroup_normal (i : ℕ) :
    (lowerRamificationGroup R G i).Normal :=
  Ideal.inertia_normal_of_forall_smul_eq fun g => pointwise_smul_maximalIdeal_pow g (i + 1)

end IsLocalRing

namespace ValuationSubring

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]

variable {K} {A : ValuationSubring L} {i : ℕ}

instance lowerRamificationGroup_normal (i : ℕ) :
    (A.lowerRamificationGroup K i).Normal :=
  IsLocalRing.lowerRamificationGroup_normal i

end ValuationSubring


/--
info: 'IsLocalRing.lowerRamificationGroup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'IsLocalRing.lowerRamificationGroup_antitone' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'IsLocalRing.lowerRamificationGroup_normal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'IsLocalRing.lowerRamificationGroup_zero_eq_ker' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'IsLocalRing.iInf_lowerRamificationGroup_eq_bot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'ValuationSubring.lowerRamificationGroup_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'ValuationSubring.lowerRamificationGroup_le_inertiaSubgroup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
