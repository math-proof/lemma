-- Carved from Lemma/Definitions/Def_AdicCompletionLocalRing.lean: instance decls only.
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Noetherian.Defs
import Lemma.AdicCompletionLocalRing.Main

set_option autoImplicit false

open IsLocalRing

namespace AdicCompletion

variable {A : Type*} [CommRing A]


section Local

variable [IsLocalRing A]

variable [IsNoetherianRing A]

instance instIsLocalRingMaximalIdeal : IsLocalRing (AdicCompletion (maximalIdeal A) A) :=
  isLocalRing_of_fg maximalIdeal_fg


end Local


end AdicCompletion

