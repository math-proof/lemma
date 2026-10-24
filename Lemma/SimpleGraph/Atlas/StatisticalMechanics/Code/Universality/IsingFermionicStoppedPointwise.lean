import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicStoppedPointwise
open StatMech StatMech.Universality


/--
[finiteUniformCoupling_fiber_abs_le_badAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedPointwise.lean)
-/
@[path]
private lemma finiteUniformCoupling_fiber_abs_le_badAt_eq
  [Fintype Omega]
  [Fintype A]
  [DecidableEq A]
  {e : Omega ≃ Omega}
  {a : A}
-- given
  (f g : Omega -> A) :
-- imply
  |((Nat.card {w : Omega // f w = a} : Nat) : Real) - ((Nat.card {w : Omega // g w = a} : Nat) : Real)| <= (Nat.card {w : Omega // f w ≠ g (e w) /\ (f w = a \/ g (e w) = a)} : Nat) := by
-- proof
  apply StatMech.Universality.finiteUniformCoupling_fiber_abs_le_badAt e f g a

/--
[isingLeapfrogStoppedKernel_reflectionCoupling_abs_le_badAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedPointwise.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_reflectionCoupling_abs_le_badAt_eq
  {R t : Nat}
  {p p' q : IsingLeapfrogBox R}
  {level : Int} :
-- imply
  |isingLeapfrogStoppedKernel R t p q - isingLeapfrogStoppedKernel R t p' q| <= (Nat.card (IsingLeapfrogStoppedCouplingBadAtFamily R t p p' q level) : Real) / (4 : Real) ^ t := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_reflectionCoupling_abs_le_badAt R t p p' q level

/--
[isingLeapfrogExitKernel_reflectionCoupling_abs_le_badAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedPointwise.lean)
-/
@[path]
private lemma isingLeapfrogExitKernel_reflectionCoupling_abs_le_badAt_eq
  {R t : Nat}
  {p p' q : IsingLeapfrogBox R}
  {level : Int} :
-- imply
  |isingLeapfrogExitKernel R t p q - isingLeapfrogExitKernel R t p' q| <= (Nat.card (IsingLeapfrogStoppedCouplingBadAtFamily R t p p' q level) : Real) / (4 : Real) ^ t := by
-- proof
  apply StatMech.Universality.isingLeapfrogExitKernel_reflectionCoupling_abs_le_badAt R t p p' q level

/--
[natCard_stoppedCouplingBadAt_le_endpointFailures](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedPointwise.lean)
-/
@[path]
private lemma natCard_stoppedCouplingBadAt_le_endpointFailures_eq
  {R t : Nat}
  {p p' q : IsingLeapfrogBox R}
  {level : Int}
-- given
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint level (isingLeapfrogBoxInt p)) :
-- imply
  Nat.card (IsingLeapfrogStoppedCouplingBadAtFamily R t p p' q level) <= Nat.card (IsingLeapfrogChoiceNoHitAtFamily R t p p' q level) + Nat.card (IsingStoppedCouplingSourceFailureAtFamily R t p p' q level) + Nat.card (IsingStoppedCouplingMirrorFailureAtFamily R t p p' q level) := by
-- proof
  apply StatMech.Universality.natCard_stoppedCouplingBadAt_le_endpointFailures R t p p' q level hmirror

/--
[isingLeapfrogStoppedKernel_reflectedStart_abs_le_of_endpointFailures](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedPointwise.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_reflectedStart_abs_le_of_endpointFailures_eq
  {R t : Nat}
  {p p' q : IsingLeapfrogBox R}
  {level : Int}
  {C : Real}
-- given
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint level (isingLeapfrogBoxInt p))
  (hfail : ((Nat.card (IsingLeapfrogChoiceNoHitAtFamily R t p p' q level) + Nat.card (IsingStoppedCouplingSourceFailureAtFamily R t p p' q level) + Nat.card (IsingStoppedCouplingMirrorFailureAtFamily R t p p' q level) : Nat) : Real) / (4 : Real) ^ t <= C) :
-- imply
  |isingLeapfrogStoppedKernel R t p q - isingLeapfrogStoppedKernel R t p' q| <= C := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_reflectedStart_abs_le_of_endpointFailures R t p p' q level hmirror C hfail

/--
[isingLeapfrogExitKernel_reflectedStart_abs_le_of_endpointFailures](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedPointwise.lean)
-/
@[path]
private lemma isingLeapfrogExitKernel_reflectedStart_abs_le_of_endpointFailures_eq
  {R t : Nat}
  {p p' q : IsingLeapfrogBox R}
  {level : Int}
  {C : Real}
-- given
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint level (isingLeapfrogBoxInt p))
  (hfail : ((Nat.card (IsingLeapfrogChoiceNoHitAtFamily R t p p' q level) + Nat.card (IsingStoppedCouplingSourceFailureAtFamily R t p p' q level) + Nat.card (IsingStoppedCouplingMirrorFailureAtFamily R t p p' q level) : Nat) : Real) / (4 : Real) ^ t <= C) :
-- imply
  |isingLeapfrogExitKernel R t p q - isingLeapfrogExitKernel R t p' q| <= C := by
-- proof
  apply StatMech.Universality.isingLeapfrogExitKernel_reflectedStart_abs_le_of_endpointFailures R t p p' q level hmirror C hfail


-- created on 2026-10-23
