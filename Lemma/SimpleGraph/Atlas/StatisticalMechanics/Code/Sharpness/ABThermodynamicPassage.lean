import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.ABThermodynamicPassage
open Filter Topology Set StatMech StatMech.Sharpness


/--
[abtp_aizenmanBarsky_of_deriv_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABThermodynamicPassage.lean)
-/
@[path]
private lemma abtp_aizenmanBarsky_of_deriv_tendsto_eq
  {J : Real}
-- given
  (Mn : Nat -> Real -> Real -> Real)
  (M : Real -> Real -> Real)
  (hfinite : forall n beta h, deriv (fun b => Mn n b h) beta <= J * (Mn n beta h * deriv (fun t => Mn n beta t) h))
  (hmag : forall beta h, Tendsto (fun n => Mn n beta h) atTop (nhds (M beta h)))
  (hbeta : forall beta h, Tendsto (fun n => deriv (fun b => Mn n b h) beta) atTop (nhds (deriv (fun b => M b h) beta)))
  (hfield : forall beta h, Tendsto (fun n => deriv (fun t => Mn n beta t) h) atTop (nhds (deriv (fun t => M beta t) h))) :
-- imply
  AizenmanBarskyInequality M J := by
-- proof
  apply StatMech.Sharpness.abtp_aizenmanBarsky_of_deriv_tendsto Mn M J hfinite hmag hbeta hfield

/--
[abtp_inequality_at_of_deriv_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABThermodynamicPassage.lean)
-/
@[path]
private lemma abtp_inequality_at_of_deriv_tendsto_eq
-- given
  (Mn : Nat -> Real -> Real -> Real)
  (M : Real -> Real -> Real)
  (J beta h : Real)
  (hfinite : forall n, deriv (fun b => Mn n b h) beta <= J * (Mn n beta h * deriv (fun t => Mn n beta t) h))
  (hmag : Tendsto (fun n => Mn n beta h) atTop (nhds (M beta h)))
  (hbeta : Tendsto (fun n => deriv (fun b => Mn n b h) beta) atTop (nhds (deriv (fun b => M b h) beta)))
  (hfield : Tendsto (fun n => deriv (fun t => Mn n beta t) h) atTop (nhds (deriv (fun t => M beta t) h))) :
-- imply
  deriv (fun b => M b h) beta <= J * (M beta h * deriv (fun t => M beta t) h) := by
-- proof
  apply StatMech.Sharpness.abtp_inequality_at_of_deriv_tendsto Mn M J beta h hfinite hmag hbeta hfield

/--
[abtp_hasDerivAt_characteristic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABThermodynamicPassage.lean)
-/
@[path]
private lemma abtp_hasDerivAt_characteristic_eq
-- given
  (F : Real -> Real -> Real)
  (b h c t : Real)
  (hF : DifferentiableAt Real (Function.uncurry F) (b + t, h - c * t)) :
-- imply
  HasDerivAt (fun s => F (b + s) (h - c * s)) (deriv (fun x => F x (h - c * t)) (b + t) - c * deriv (fun y => F (b + t) y) (h - c * t)) t := by
-- proof
  apply StatMech.Sharpness.abtp_hasDerivAt_characteristic F b h c t hF

/--
[abtp_inequality_at_of_characteristics](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABThermodynamicPassage.lean)
-/
@[path]
private lemma abtp_inequality_at_of_characteristics_eq
-- given
  (Mn : Nat -> Real -> Real -> Real)
  (M : Real -> Real -> Real)
  (J beta h : Real)
  (hJ : 0 <= J)
  (hM : 0 <= M beta h)
  (hfinite : forall n b t, deriv (fun x => Mn n x t) b <= J * (Mn n b t * deriv (fun y => Mn n b y) t))
  (hfield : forall n b t, 0 <= deriv (fun y => Mn n b y) t)
  (hmonoBeta : forall n t, Monotone (fun b => Mn n b t))
  (hmonoField : forall n b, Monotone (fun t => Mn n b t))
  (hle : forall n b t, Mn n b t <= M b t)
  (hconv : forall b t, Tendsto (fun n => Mn n b t) atTop (nhds (M b t)))
  (hcontBeta : ContinuousAt (fun b => M b h) beta)
  (hlineFinite : forall n c t, HasDerivAt (fun s => Mn n (beta + s) (h - c * s)) (deriv (fun b => Mn n b (h - c * t)) (beta + t) - c * deriv (fun y => Mn n (beta + t) y) (h - c * t)) t)
  (hlineLimit : forall c, HasDerivAt (fun s => M (beta + s) (h - c * s)) (deriv (fun b => M b h) beta - c * deriv (fun y => M beta y) h) 0) :
-- imply
  deriv (fun b => M b h) beta <= J * (M beta h * deriv (fun y => M beta y) h) := by
-- proof
  apply StatMech.Sharpness.abtp_inequality_at_of_characteristics Mn M J beta h hJ hM hfinite hfield hmonoBeta hmonoField hle hconv hcontBeta hlineFinite hlineLimit

/--
[abtp_inequality_at_of_jointDifferentiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABThermodynamicPassage.lean)
-/
@[path]
private lemma abtp_inequality_at_of_jointDifferentiable_eq
-- given
  (Mn : Nat -> Real -> Real -> Real)
  (M : Real -> Real -> Real)
  (J beta h : Real)
  (hJ : 0 <= J)
  (hM : 0 <= M beta h)
  (hfinite : forall n b t, deriv (fun x => Mn n x t) b <= J * (Mn n b t * deriv (fun y => Mn n b y) t))
  (hfield : forall n b t, 0 <= deriv (fun y => Mn n b y) t)
  (hmonoBeta : forall n t, Monotone (fun b => Mn n b t))
  (hmonoField : forall n b, Monotone (fun t => Mn n b t))
  (hle : forall n b t, Mn n b t <= M b t)
  (hconv : forall b t, Tendsto (fun n => Mn n b t) atTop (nhds (M b t)))
  (hcontBeta : ContinuousAt (fun b => M b h) beta)
  (hjointFinite : forall n b t, DifferentiableAt Real (Function.uncurry (Mn n)) (b, t))
  (hjointLimit : DifferentiableAt Real (Function.uncurry M) (beta, h)) :
-- imply
  deriv (fun b => M b h) beta <= J * (M beta h * deriv (fun y => M beta y) h) := by
-- proof
  apply StatMech.Sharpness.abtp_inequality_at_of_jointDifferentiable Mn M J beta h hJ hM hfinite hfield hmonoBeta hmonoField hle hconv hcontBeta hjointFinite hjointLimit

/--
[abtp_inequality_at_of_characteristics_physical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABThermodynamicPassage.lean)
-/
@[path]
private lemma abtp_inequality_at_of_characteristics_physical_eq
-- given
  (Mn Cn : Nat -> Real -> Real -> Real)
  (M : Real -> Real -> Real)
  (J beta h : Real)
  (hJ : 0 <= J)
  (hbeta : 0 <= beta)
  (hh : 0 < h)
  (hM : 0 <= M beta h)
  (hfinite : forall n b t, 0 <= b -> 0 <= t -> deriv (fun x => Mn n x t) b <= J * (Cn n b t * deriv (fun y => Mn n b y) t))
  (hfield : forall n b t, 0 <= b -> 0 <= t -> 0 <= deriv (fun y => Mn n b y) t)
  (hmonoBeta : forall n t, 0 <= t -> MonotoneOn (fun b => Cn n b t) (Ici 0))
  (hmonoField : forall n b, 0 <= b -> MonotoneOn (fun t => Cn n b t) (Ici 0))
  (hle : forall n b t, 0 <= b -> 0 <= t -> Cn n b t <= M b t)
  (hconv : forall b t, 0 <= b -> 0 <= t -> Tendsto (fun n => Mn n b t) atTop (nhds (M b t)))
  (hcontBeta : ContinuousAt (fun b => M b h) beta)
  (hlineFinite : forall n c t, HasDerivAt (fun s => Mn n (beta + s) (h - c * s)) (deriv (fun b => Mn n b (h - c * t)) (beta + t) - c * deriv (fun y => Mn n (beta + t) y) (h - c * t)) t)
  (hlineLimit : forall c, HasDerivAt (fun s => M (beta + s) (h - c * s)) (deriv (fun b => M b h) beta - c * deriv (fun y => M beta y) h) 0) :
-- imply
  deriv (fun b => M b h) beta <= J * (M beta h * deriv (fun y => M beta y) h) := by
-- proof
  apply StatMech.Sharpness.abtp_inequality_at_of_characteristics_physical Mn Cn M J beta h hJ hbeta hh hM hfinite hfield hmonoBeta hmonoField hle hconv hcontBeta hlineFinite hlineLimit

/--
[abtp_inequality_at_of_partialDifferentiable_physical_envelope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABThermodynamicPassage.lean)
-/
@[path]
private lemma abtp_inequality_at_of_partialDifferentiable_physical_envelope_eq
-- given
  (Mn Cn : Nat -> Real -> Real -> Real)
  (M : Real -> Real -> Real)
  (J beta h : Real)
  (hJ : 0 <= J)
  (hbeta : 0 <= beta)
  (hh : 0 < h)
  (hM : 0 <= M beta h)
  (hfinite : forall n b t, 0 <= b -> 0 <= t -> deriv (fun x => Mn n x t) b <= J * (Cn n b t * deriv (fun y => Mn n b y) t))
  (hfield : forall n b t, 0 <= b -> 0 <= t -> 0 <= deriv (fun y => Mn n b y) t)
  (hmonoBeta : forall n t, 0 <= t -> MonotoneOn (fun b => Cn n b t) (Ici 0))
  (hmonoField : forall n b, 0 <= b -> MonotoneOn (fun t => Cn n b t) (Ici 0))
  (hle : forall n b t, 0 <= b -> 0 <= t -> Cn n b t <= M b t)
  (hconv : forall b t, 0 <= b -> 0 <= t -> Tendsto (fun n => Mn n b t) atTop (nhds (M b t)))
  (hcont : ContinuousAt (Function.uncurry M) (beta, h))
  (hjointFinite : forall n b t, DifferentiableAt Real (Function.uncurry (Mn n)) (b, t))
  (hbetaLimit : DifferentiableAt Real (fun b => M b h) beta)
  (hfieldLimit : DifferentiableAt Real (fun t => M beta t) h) :
-- imply
  deriv (fun b => M b h) beta <= J * (M beta h * deriv (fun y => M beta y) h) := by
-- proof
  apply StatMech.Sharpness.abtp_inequality_at_of_partialDifferentiable_physical_envelope Mn Cn M J beta h hJ hbeta hh hM hfinite hfield hmonoBeta hmonoField hle hconv hcont hjointFinite hbetaLimit hfieldLimit

/--
[abtp_inequality_at_of_fieldDifferentiable_physical_envelope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABThermodynamicPassage.lean)
-/
@[path]
private lemma abtp_inequality_at_of_fieldDifferentiable_physical_envelope_eq
-- given
  (Mn Cn : Nat -> Real -> Real -> Real)
  (M : Real -> Real -> Real)
  (J beta h : Real)
  (hJ : 0 <= J)
  (hbeta : 0 <= beta)
  (hh : 0 < h)
  (hM : 0 <= M beta h)
  (hfinite : forall n b t, 0 <= b -> 0 <= t -> deriv (fun x => Mn n x t) b <= J * (Cn n b t * deriv (fun y => Mn n b y) t))
  (hfield : forall n b t, 0 <= b -> 0 <= t -> 0 <= deriv (fun y => Mn n b y) t)
  (hmonoBeta : forall n t, 0 <= t -> MonotoneOn (fun b => Cn n b t) (Ici 0))
  (hmonoField : forall n b, 0 <= b -> MonotoneOn (fun t => Cn n b t) (Ici 0))
  (hle : forall n b t, 0 <= b -> 0 <= t -> Cn n b t <= M b t)
  (hconv : forall b t, 0 <= b -> 0 <= t -> Tendsto (fun n => Mn n b t) atTop (nhds (M b t)))
  (hcont : ContinuousAt (Function.uncurry M) (beta, h))
  (hjointFinite : forall n b t, DifferentiableAt Real (Function.uncurry (Mn n)) (b, t))
  (hfieldLimit : DifferentiableAt Real (fun t => M beta t) h)
  (hfieldNN : 0 <= deriv (fun t => M beta t) h) :
-- imply
  deriv (fun b => M b h) beta <= J * (M beta h * deriv (fun y => M beta y) h) := by
-- proof
  apply StatMech.Sharpness.abtp_inequality_at_of_fieldDifferentiable_physical_envelope Mn Cn M J beta h hJ hbeta hh hM hfinite hfield hmonoBeta hmonoField hle hconv hcont hjointFinite hfieldLimit hfieldNN

/--
[abtp_inequality_at_of_jointDifferentiable_physical_envelope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABThermodynamicPassage.lean)
-/
@[path]
private lemma abtp_inequality_at_of_jointDifferentiable_physical_envelope_eq
-- given
  (Mn Cn : Nat -> Real -> Real -> Real)
  (M : Real -> Real -> Real)
  (J beta h : Real)
  (hJ : 0 <= J)
  (hbeta : 0 <= beta)
  (hh : 0 < h)
  (hM : 0 <= M beta h)
  (hfinite : forall n b t, 0 <= b -> 0 <= t -> deriv (fun x => Mn n x t) b <= J * (Cn n b t * deriv (fun y => Mn n b y) t))
  (hfield : forall n b t, 0 <= b -> 0 <= t -> 0 <= deriv (fun y => Mn n b y) t)
  (hmonoBeta : forall n t, 0 <= t -> MonotoneOn (fun b => Cn n b t) (Ici 0))
  (hmonoField : forall n b, 0 <= b -> MonotoneOn (fun t => Cn n b t) (Ici 0))
  (hle : forall n b t, 0 <= b -> 0 <= t -> Cn n b t <= M b t)
  (hconv : forall b t, 0 <= b -> 0 <= t -> Tendsto (fun n => Mn n b t) atTop (nhds (M b t)))
  (hcontBeta : ContinuousAt (fun b => M b h) beta)
  (hjointFinite : forall n b t, DifferentiableAt Real (Function.uncurry (Mn n)) (b, t))
  (hjointLimit : DifferentiableAt Real (Function.uncurry M) (beta, h)) :
-- imply
  deriv (fun b => M b h) beta <= J * (M beta h * deriv (fun y => M beta y) h) := by
-- proof
  apply StatMech.Sharpness.abtp_inequality_at_of_jointDifferentiable_physical_envelope Mn Cn M J beta h hJ hbeta hh hM hfinite hfield hmonoBeta hmonoField hle hconv hcontBeta hjointFinite hjointLimit

/--
[abtp_inequality_at_of_jointDifferentiable_physical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABThermodynamicPassage.lean)
-/
@[path]
private lemma abtp_inequality_at_of_jointDifferentiable_physical_eq
-- given
  (Mn : Nat -> Real -> Real -> Real)
  (M : Real -> Real -> Real)
  (J beta h : Real)
  (hJ : 0 <= J)
  (hbeta : 0 <= beta)
  (hh : 0 < h)
  (hM : 0 <= M beta h)
  (hfinite : forall n b t, 0 <= b -> 0 <= t -> deriv (fun x => Mn n x t) b <= J * (Mn n b t * deriv (fun y => Mn n b y) t))
  (hfield : forall n b t, 0 <= b -> 0 <= t -> 0 <= deriv (fun y => Mn n b y) t)
  (hmonoBeta : forall n t, 0 <= t -> MonotoneOn (fun b => Mn n b t) (Ici 0))
  (hmonoField : forall n b, 0 <= b -> MonotoneOn (fun t => Mn n b t) (Ici 0))
  (hle : forall n b t, 0 <= b -> 0 <= t -> Mn n b t <= M b t)
  (hconv : forall b t, 0 <= b -> 0 <= t -> Tendsto (fun n => Mn n b t) atTop (nhds (M b t)))
  (hcontBeta : ContinuousAt (fun b => M b h) beta)
  (hjointFinite : forall n b t, DifferentiableAt Real (Function.uncurry (Mn n)) (b, t))
  (hjointLimit : DifferentiableAt Real (Function.uncurry M) (beta, h)) :
-- imply
  deriv (fun b => M b h) beta <= J * (M beta h * deriv (fun y => M beta y) h) := by
-- proof
  apply StatMech.Sharpness.abtp_inequality_at_of_jointDifferentiable_physical Mn M J beta h hJ hbeta hh hM hfinite hfield hmonoBeta hmonoField hle hconv hcontBeta hjointFinite hjointLimit

/--
[abtp_aizenmanBarskyPhysical_of_jointDifferentiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABThermodynamicPassage.lean)
-/
@[path]
private lemma abtp_aizenmanBarskyPhysical_of_jointDifferentiable_eq
  {J : Real}
-- given
  (Mn : Nat -> Real -> Real -> Real)
  (M : Real -> Real -> Real)
  (hJ : 0 <= J)
  (hM : forall beta h, 0 <= beta -> 0 < h -> 0 <= M beta h)
  (hfinite : forall n b t, 0 <= b -> 0 <= t -> deriv (fun x => Mn n x t) b <= J * (Mn n b t * deriv (fun y => Mn n b y) t))
  (hfield : forall n b t, 0 <= b -> 0 <= t -> 0 <= deriv (fun y => Mn n b y) t)
  (hmonoBeta : forall n t, 0 <= t -> MonotoneOn (fun b => Mn n b t) (Ici 0))
  (hmonoField : forall n b, 0 <= b -> MonotoneOn (fun t => Mn n b t) (Ici 0))
  (hle : forall n b t, 0 <= b -> 0 <= t -> Mn n b t <= M b t)
  (hconv : forall b t, 0 <= b -> 0 <= t -> Tendsto (fun n => Mn n b t) atTop (nhds (M b t)))
  (hjointFinite : forall n b t, DifferentiableAt Real (Function.uncurry (Mn n)) (b, t))
  (hjointLimit : forall beta h, 0 <= beta -> 0 < h -> DifferentiableAt Real (Function.uncurry M) (beta, h)) :
-- imply
  AizenmanBarskyInequalityPhysical M J := by
-- proof
  apply StatMech.Sharpness.abtp_aizenmanBarskyPhysical_of_jointDifferentiable Mn M J hJ hM hfinite hfield hmonoBeta hmonoField hle hconv hjointFinite hjointLimit


-- created on 2026-10-23
