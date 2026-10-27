import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.ABMeanfieldGhost
open Finset Set SimpleGraph StatMech StatMech.Sharpness


/--
[abmg_meanfield_target_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABMeanfieldGhost.lean)
-/
@[path]
private lemma abmg_meanfield_target_finite_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {B : Set (Option V)}
-- given
  (J : Sym2 V -> Real)
  (beta h m : Real)
  (hJ : ∀ e ∈ G.edgeFinset, 0 <= J e)
  (hbeta : 0 <= beta)
  (hh : 0 <= h)
  (hm : ∀ S : Finset (Option V), some o ∈ S -> (mpiSurfaceEvent (withGhost G) B S).Nonempty -> m <= abmgTargetPhi G J o B beta h S) :
-- imply
  m * (1 - abmgTargetMag G J o B beta h) <= beta * deriv (fun b => abmgTargetMag G J o B b h) beta := by
-- proof
  apply StatMech.Sharpness.abmg_meanfield_target_finite G J o B beta h m hJ hbeta hh hm

/--
[abmg_meanfield_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABMeanfieldGhost.lean)
-/
@[path]
private lemma abmg_meanfield_finite_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (J : Sym2 V -> Real)
  (beta h m : Real)
  (hJ : ∀ e ∈ G.edgeFinset, 0 <= J e)
  (hbeta : 0 <= beta)
  (hh : 0 <= h)
  (hm : ∀ S : Finset (Option V), some o ∈ S -> (mpiSurfaceEvent (withGhost G) {none} S).Nonempty -> m <= abmgPhi G J o beta h S) :
-- imply
  m * (1 - abfaMag G J o beta h) <= beta * deriv (fun b => abfaMag G J o b h) beta := by
-- proof
  apply StatMech.Sharpness.abmg_meanfield_finite G J o beta h m hJ hbeta hh hm


-- created on 2026-10-23
