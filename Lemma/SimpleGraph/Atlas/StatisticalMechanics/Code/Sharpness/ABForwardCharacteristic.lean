import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.ABForwardCharacteristic
open Filter Set Topology StatMech StatMech.Sharpness


/--
[abfc_forward_characteristic_physical_envelope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABForwardCharacteristic.lean)
-/
@[path]
private lemma abfc_forward_characteristic_physical_envelope_eq
  {Mn Cn : Nat → Real → Real → Real}
  {M : Real → Real → Real}
-- given
  (J beta h : Real)
  (hJ : 0 ≤ J)
  (hbeta : 0 ≤ beta)
  (hh : 0 < h)
  (hM : 0 ≤ M beta h)
  (hfinite : ∀ n b t, 0 ≤ b → 0 ≤ t → deriv (fun x ↦ Mn n x t) b ≤ J * (Cn n b t * deriv (fun y ↦ Mn n b y) t))
  (hfield : ∀ n b t, 0 ≤ b → 0 ≤ t → 0 ≤ deriv (fun y ↦ Mn n b y) t)
  (hmonoBeta : ∀ n t, 0 ≤ t → MonotoneOn (fun b ↦ Cn n b t) (Ici 0))
  (hmonoField : ∀ n b, 0 ≤ b → MonotoneOn (fun t ↦ Cn n b t) (Ici 0))
  (hle : ∀ n b t, 0 ≤ b → 0 ≤ t → Cn n b t ≤ M b t)
  (hconv : ∀ b t, 0 ≤ b → 0 ≤ t → Tendsto (fun n ↦ Mn n b t) atTop (nhds (M b t)))
  (hcont : ContinuousAt (Function.uncurry M) (beta, h))
  (hjointFinite : ∀ n b t, DifferentiableAt Real (Function.uncurry (Mn n)) (b, t)) :
-- imply
  ∀ epsilon, 0 < epsilon → ∃ d > 0, ∀ t ∈ Icc (0 : Real) d, M (beta + t) h ≤ M beta (h + (J * (M beta h + epsilon)) * t) := by
-- proof
  apply StatMech.Sharpness.abfc_forward_characteristic_physical_envelope Mn Cn M J beta h hJ hbeta hh hM hfinite hfield hmonoBeta hmonoField hle hconv hcont hjointFinite

/--
[abfc_abig_forward_characteristic_of_exhaustion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABForwardCharacteristic.lean)
-/
@[path]
private lemma abfc_abig_forward_characteristic_of_exhaustion_eq
  [Countable V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → Real}
  {o : V}
  {S : Nat → Finset V}
-- given
  (J0 beta h : Real)
  (hJ0 : 0 ≤ J0)
  (hbeta : 0 ≤ beta)
  (hh : 0 < h)
  (hJ : ∀ e, 0 ≤ J e)
  (hJsupport : ∀ x y, ¬ G.Adj x y → J s(x, y) = 0)
  (ho : ∀ n, o ∈ S n)
  (hrow : ∀ n (x : S n), abcrIncidentCoupling (abigWindowGraph G (S n)) (abigWindowCoupling J (S n)) x ≤ J0)
  (hInfiniteTarget : ∀ b t, 0 ≤ b → 0 ≤ t → ∀ n (x : S n), abigMag G J (x : V) b t ≤ abigMag G J o b t)
  (hmonoWindow : Monotone (fun n ↦ abigGhostWindow (S n)))
  (hcover : ∀ F : Finset (Option V), ∃ n, F ⊆ abigGhostWindow (S n)) :
-- imply
  ∀ epsilon, 0 < epsilon → ∃ d > 0, ∀ t ∈ Icc (0 : Real) d, abigMag G J o (beta + t) h ≤ abigMag G J o beta (h + (J0 * (abigMag G J o beta h + epsilon)) * t) := by
-- proof
  apply StatMech.Sharpness.abfc_abig_forward_characteristic_of_exhaustion G J o J0 beta h hJ0 hbeta hh hJ hJsupport S ho hrow hInfiniteTarget hmonoWindow hcover


-- created on 2026-10-23
