import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.ABBoundaryProfile.Part2
open Finset Set SimpleGraph StatMech StatMech.Sharpness


/--
[none_mem_abbTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryProfile.lean)
-/
@[path]
private lemma none_mem_abbTarget_eq
  {d n : Nat} :
-- imply
  none ∈ abbTarget d n := by
-- proof
  apply StatMech.Sharpness.none_mem_abbTarget d n

/--
[some_mem_abbTarget_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryProfile.lean)
-/
@[path]
private lemma some_mem_abbTarget_iff_eq
  {d n : Nat}
  {x : sctBox d n} :
-- imply
  some x ∈ abbTarget d n ↔ (x : Site d) ∈ vertexBoundary d n := by
-- proof
  apply StatMech.Sharpness.some_mem_abbTarget_iff d n x

/--
[abbMag_differentiableAt_joint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryProfile.lean)
-/
@[path]
private lemma abbMag_differentiableAt_joint_eq
  {d n : Nat}
-- given
  (beta h : Real) :
-- imply
  DifferentiableAt Real (Function.uncurry (abbMag d n)) (beta, h) := by
-- proof
  apply StatMech.Sharpness.abbMag_differentiableAt_joint d n beta h

/--
[abbMag_meanfield](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryProfile.lean)
-/
@[path]
private lemma abbMag_meanfield_eq
  {d n : Nat}
-- given
  (beta h : Real)
  (hbeta : 0 <= beta)
  (hh : 0 <= h)
  (hphi : ∀ S : Finset (Option (sctBox d n)), some (sctBoxOrigin d n) ∈ S -> (mpiSurfaceEvent (withGhost (sctBoxGraph d n)) (abbTarget d n) S).Nonempty -> 1 <= abbPhi d n beta h S) :
-- imply
  1 - abbMag d n beta h <= beta * deriv (fun b => abbMag d n b h) beta := by
-- proof
  apply StatMech.Sharpness.abbMag_meanfield d n beta h hbeta hh hphi

/--
[abbMag_aizenmanBarsky_le_envelope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryProfile.lean)
-/
@[path]
private lemma abbMag_aizenmanBarsky_le_envelope_eq
  {d n : Nat}
-- given
  (beta h J0 U : Real)
  (hrow : ∀ x, abcrIncidentCoupling (sctBoxGraph d n) (abbCoupling d n) x <= J0)
  (hbeta : 0 <= beta)
  (hh : 0 <= h)
  (hU : 0 <= U)
  (htarget : ∀ x : sctBox d n, probV (abfaParams (sctBoxGraph d n) (abbCoupling d n) beta h) (connEvent (withGhost (sctBoxGraph d n)) Set.univ (some x) (abbTarget d n)) <= U) :
-- imply
  deriv (fun b => abbMag d n b h) beta <= J0 * U * deriv (fun t => abbMag d n beta t) h := by
-- proof
  apply StatMech.Sharpness.abbMag_aizenmanBarsky_le_envelope d n beta h J0 U hrow hbeta hh hU htarget


-- created on 2026-10-23
