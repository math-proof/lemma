-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_ProjSpaceCechTwist.lean: instance decls only.
import Mathlib
import Lemma.AlgebraicGeometry.ProjSpaceCechTwist

set_option autoImplicit false

noncomputable section

universe u

open Finset Function

namespace ProjSpaceCech

section Setup

variable (n : ℕ)

instance Twist.Mon.instDecidableEq (d : ℤ) (I : Finset (Fin (n + 1))) :
    DecidableEq (Twist.Mon n d I) := Classical.decEq _

end Setup

section AltCech

variable (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)

instance Idx.instFintype (i : ℕ) : Fintype (Idx n i) := Subtype.fintype _

instance Idx.instDecidableEq (i : ℕ) : DecidableEq (Idx n i) := Classical.decEq _

instance Twist.cochain.instAddCommGroup (i : ℕ) : AddCommGroup (Twist.cochain R n d i) :=
  inferInstanceAs (AddCommGroup (∀ s, _ →₀ R))

instance Twist.cochain.instModule (i : ℕ) : Module R (Twist.cochain R n d i) :=
  inferInstanceAs (Module R (∀ s, _ →₀ R))

end AltCech


section Cohomology

variable (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)

instance Twist.H.addCommGroup (i : ℕ) : AddCommGroup (Twist.H R n d i) :=
  match i with
  | 0 => inferInstanceAs (AddCommGroup
      ↥(LinearMap.ker (Twist.d R n d 0)))
  | (j + 1) => inferInstanceAs (AddCommGroup
      (↥(LinearMap.ker (Twist.d R n d (j + 1))) ⧸ _))

instance Twist.H.module (i : ℕ) : Module R (Twist.H R n d i) :=
  match i with
  | 0 => inferInstanceAs (Module R
      ↥(LinearMap.ker (Twist.d R n d 0)))
  | (j + 1) => inferInstanceAs (Module R
      (↥(LinearMap.ker (Twist.d R n d (j + 1))) ⧸ _))

end Cohomology

end ProjSpaceCech

end
