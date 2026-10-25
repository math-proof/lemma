import Mathlib

universe u

open IsLocalRing

def SmoothFieldFiberRegularStalksInput : Prop :=
  ∀ (k A : Type u) [Field k] [CommRing A] [Algebra k A],
    Algebra.Smooth k A → ∀ (p : Ideal A) [p.IsPrime],
      IsRegularLocalRing (Localization.AtPrime p)

namespace SmoothFieldFiberRegularStalks


end SmoothFieldFiberRegularStalks

/--
info: 'SmoothFieldFiberRegularStalks.isRegularLocalRing_localization_atPrime_of_isArtinianRing_of_isReduced' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SmoothFieldFiberRegularStalks.isRegularLocalRing_localization_atPrime_of_isArtinianRing_of_isReduced

/--
info: 'SmoothFieldFiberRegularStalks.isRegularRing_of_isArtinianRing_of_isReduced' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SmoothFieldFiberRegularStalks.isRegularRing_of_isArtinianRing_of_isReduced

/--
info: 'SmoothFieldFiberRegularStalks.isRegularLocalRing_localization_atPrime_of_formallyUnramified' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SmoothFieldFiberRegularStalks.isRegularLocalRing_localization_atPrime_of_formallyUnramified

/--
info: 'SmoothFieldFiberRegularStalks.isRegularLocalRing_localization_atPrime_of_etale' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SmoothFieldFiberRegularStalks.isRegularLocalRing_localization_atPrime_of_etale

/--
info: 'SmoothFieldFiberRegularStalks.isRegularRing_of_etale' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SmoothFieldFiberRegularStalks.isRegularRing_of_etale

/--
info: 'SmoothFieldFiberRegularStalks.isRegularRing_of_smooth_of_input' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SmoothFieldFiberRegularStalks.isRegularRing_of_smooth_of_input

/--
info: 'SmoothFieldFiberRegularStalks.not_isRegularLocalRing_dualNumber' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SmoothFieldFiberRegularStalks.not_isRegularLocalRing_dualNumber

/--
info: 'SmoothFieldFiberRegularStalks.not_isRegularLocalRing_localization_atPrime_dualNumber' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SmoothFieldFiberRegularStalks.not_isRegularLocalRing_localization_atPrime_dualNumber

/--
info: 'SmoothFieldFiberRegularStalks.not_forall_regular_stalks_without_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SmoothFieldFiberRegularStalks.not_forall_regular_stalks_without_smooth
