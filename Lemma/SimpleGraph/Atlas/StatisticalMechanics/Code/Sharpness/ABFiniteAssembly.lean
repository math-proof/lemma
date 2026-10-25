import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.ABFiniteAssembly.Part2
open Finset Set SimpleGraph StatMech StatMech.Sharpness


/--
[abfaLiftCoupling_some_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteAssembly.lean)
-/
@[path]
private lemma abfaLiftCoupling_some_some_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {x y : V} :
-- imply
  abfaLiftCoupling G J s(some x, some y) = if s(x, y) ∈ G.edgeFinset then J s(x, y) else 0 := by
-- proof
  apply StatMech.Sharpness.abfaLiftCoupling_some_some G J x y

/--
[abfaLiftCoupling_some_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteAssembly.lean)
-/
@[path]
private lemma abfaLiftCoupling_some_none_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {x : V} :
-- imply
  abfaLiftCoupling G J s(some x, none) = 0 := by
-- proof
  apply StatMech.Sharpness.abfaLiftCoupling_some_none G J x

/--
[abfa_differentiableAt_mag_joint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteAssembly.lean)
-/
@[path]
private lemma abfa_differentiableAt_mag_joint_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {o : V}
-- given
  (beta h : ℝ) :
-- imply
  DifferentiableAt ℝ (Function.uncurry (abfaMag G J o)) (beta, h) := by
-- proof
  apply StatMech.Sharpness.abfa_differentiableAt_mag_joint G J o beta h

/--
[abfa_differentiableAt_prob_joint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteAssembly.lean)
-/
@[path]
private lemma abfa_differentiableAt_prob_joint_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {A : Set (ConfigSpace (Sym2 (Option V)))}
-- given
  (beta h : ℝ) :
-- imply
  DifferentiableAt ℝ (Function.uncurry (fun b t => probV (abfaParams G J b t) A)) (beta, h) := by
-- proof
  apply StatMech.Sharpness.abfa_differentiableAt_prob_joint G J A beta h

/--
[abfaLiftCoupling_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteAssembly.lean)
-/
@[path]
private lemma abfaLiftCoupling_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {e : Sym2 (Option V)}
-- given
  (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e) :
-- imply
  0 ≤ abfaLiftCoupling G J e := by
-- proof
  apply StatMech.Sharpness.abfaLiftCoupling_nonneg G J hJ e

/--
[abfaParams_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteAssembly.lean)
-/
@[path]
private lemma abfaParams_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {e : Sym2 (Option V)}
-- given
  (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e)
  (beta h : ℝ)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ abfaParams G J beta h e ∧ abfaParams G J beta h e ≤ 1 := by
-- proof
  apply StatMech.Sharpness.abfaParams_mem G J hJ beta h hbeta hh e

/--
[abfa_deriv_beta_eq_origEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteAssembly.lean)
-/
@[path]
private lemma abfa_deriv_beta_eq_origEdges_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {o : V}
-- given
  (beta h : ℝ) :
-- imply
  deriv (fun b => abfaMag G J o b h) beta = ∑ e ∈ FieldGhostDict.origEdges G, abfaLiftCoupling G J e * probV (abfaParams G J beta h) (abgiClosedPivotal e (connEvent (withGhost G) Set.univ (some o) {none})) := by
-- proof
  apply StatMech.Sharpness.abfa_deriv_beta_eq_origEdges G J o beta h

/--
[abfa_deriv_beta_connTarget_eq_origEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteAssembly.lean)
-/
@[path]
private lemma abfa_deriv_beta_connTarget_eq_origEdges_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {o : V}
  {B : Set (Option V)}
-- given
  (beta h : ℝ) :
-- imply
  deriv (fun b => probV (abfaParams G J b h) (connEvent (withGhost G) Set.univ (some o) B)) beta = ∑ e ∈ FieldGhostDict.origEdges G, abfaLiftCoupling G J e * probV (abfaParams G J beta h) (abgiClosedPivotal e (connEvent (withGhost G) Set.univ (some o) B)) := by
-- proof
  apply StatMech.Sharpness.abfa_deriv_beta_connTarget_eq_origEdges G J o B beta h

/--
[abfa_deriv_beta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteAssembly.lean)
-/
@[path]
private lemma abfa_deriv_beta_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {o : V}
-- given
  (beta h : ℝ)
  (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ deriv (fun b => abfaMag G J o b h) beta := by
-- proof
  apply StatMech.Sharpness.abfa_deriv_beta_nonneg G J o beta h hJ hbeta hh

/--
[abfa_deriv_field_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteAssembly.lean)
-/
@[path]
private lemma abfa_deriv_field_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {o : V}
-- given
  (beta h : ℝ)
  (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ deriv (fun t => abfaMag G J o beta t) h := by
-- proof
  apply StatMech.Sharpness.abfa_deriv_field_nonneg G J o beta h hJ hbeta hh

/--
[abfaMag_monotoneOn_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteAssembly.lean)
-/
@[path]
private lemma abfaMag_monotoneOn_beta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {o : V}
-- given
  (h : ℝ)
  (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e)
  (hh : 0 ≤ h) :
-- imply
  MonotoneOn (fun beta => abfaMag G J o beta h) (Set.Ici 0) := by
-- proof
  apply StatMech.Sharpness.abfaMag_monotoneOn_beta G J o h hJ hh

/--
[abfaMag_monotoneOn_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteAssembly.lean)
-/
@[path]
private lemma abfaMag_monotoneOn_field_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {o : V}
  {beta : ℝ}
-- given
  (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e)
  (hbeta : 0 ≤ beta) :
-- imply
  MonotoneOn (fun h => abfaMag G J o beta h) (Set.Ici 0) := by
-- proof
  apply StatMech.Sharpness.abfaMag_monotoneOn_field G J o beta hJ hbeta

/--
[abfa_aizenmanBarsky](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteAssembly.lean)
-/
@[path]
private lemma abfa_aizenmanBarsky_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {o : V}
-- given
  (beta h J0 : ℝ)
  (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e)
  (hrow : ∀ x, abcrIncidentCoupling G J x = J0)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h)
  (hmag : ∀ x : V, probV (abfaParams G J beta h) (connEvent (withGhost G) Set.univ (some x) {none}) = abfaMag G J o beta h) :
-- imply
  deriv (fun b => abfaMag G J o b h) beta ≤ J0 * abfaMag G J o beta h * deriv (fun t => abfaMag G J o beta t) h := by
-- proof
  apply StatMech.Sharpness.abfa_aizenmanBarsky G J o beta h J0 hJ hrow hbeta hh hmag

/--
[abfa_aizenmanBarsky_le_envelope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteAssembly.lean)
-/
@[path]
private lemma abfa_aizenmanBarsky_le_envelope_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {o : V}
-- given
  (beta h J0 U : ℝ)
  (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e)
  (hrow : ∀ x, abcrIncidentCoupling G J x ≤ J0)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h)
  (hU : 0 ≤ U)
  (htarget : ∀ x : V, probV (abfaParams G J beta h) (connEvent (withGhost G) Set.univ (some x) {none}) ≤ U) :
-- imply
  deriv (fun b => abfaMag G J o b h) beta ≤ J0 * U * deriv (fun t => abfaMag G J o beta t) h := by
-- proof
  apply StatMech.Sharpness.abfa_aizenmanBarsky_le_envelope G J o beta h J0 U hJ hrow hbeta hh hU htarget

/--
[abfa_aizenmanBarsky_target_le_envelope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteAssembly.lean)
-/
@[path]
private lemma abfa_aizenmanBarsky_target_le_envelope_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {o : V}
  {B : Set (Option V)}
-- given
  (beta h J0 U : ℝ)
  (hghost : none ∈ B)
  (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e)
  (hrow : ∀ x, abcrIncidentCoupling G J x ≤ J0)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h)
  (hU : 0 ≤ U)
  (htarget : ∀ x : V, probV (abfaParams G J beta h) (connEvent (withGhost G) Set.univ (some x) B) ≤ U) :
-- imply
  deriv (fun b => probV (abfaParams G J b h) (connEvent (withGhost G) Set.univ (some o) B)) beta ≤ J0 * U * deriv (fun t => probV (abfaParams G J beta t) (connEvent (withGhost G) Set.univ (some o) B)) h := by
-- proof
  apply StatMech.Sharpness.abfa_aizenmanBarsky_target_le_envelope G J o B beta h J0 U hghost hJ hrow hbeta hh hU htarget


-- created on 2026-10-23
