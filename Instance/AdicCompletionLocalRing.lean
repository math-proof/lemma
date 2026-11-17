-- Carved from Lemma/Definitions/Def_AdicCompletionLocalRing.lean: instance decls only.

module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Noetherian.Defs

@[expose] public section

set_option autoImplicit false

open IsLocalRing

namespace AdicCompletion

variable {A : Type*} [CommRing A]


section Local

variable [IsLocalRing A]

variable [IsNoetherianRing A]

instance instIsLocalRingMaximalIdeal : IsLocalRing (AdicCompletion (maximalIdeal A) A) :=
  isLocalRing_of_fg (IsNoetherian.noetherian _)


end Local


end AdicCompletion

