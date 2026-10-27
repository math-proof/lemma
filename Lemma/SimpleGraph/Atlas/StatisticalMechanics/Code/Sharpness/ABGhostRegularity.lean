import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.ABGhostRegularity.Part7
open Filter Finset Set SimpleGraph Topology Asymptotics StatMech StatMech.Sharpness


/--
[abgr_sum_configWeightV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgr_sum_configWeightV_eq
  [Fintype E]
  [DecidableEq E]
-- given
  (p : E -> Real) :
-- imply
  ∑ omega : ConfigSpace E, configWeightV p omega = 1 := by
-- proof
  apply StatMech.Sharpness.abgr_sum_configWeightV p

/--
[abgr_probV_allClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgr_probV_allClosed_eq
  [Fintype E]
  [DecidableEq E]
  {t : Finset E}
-- given
  (p : E -> Real) :
-- imply
  probV p {omega | ∀ e ∈ t, omega e = false} = ∏ e ∈ t, (1 - p e) := by
-- proof
  apply StatMech.Sharpness.abgr_probV_allClosed p t

/--
[abgr_probV_anyOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgr_probV_anyOpen_eq
  [Fintype E]
  [DecidableEq E]
  {t : Finset E}
-- given
  (p : E -> Real) :
-- imply
  probV p {omega | ∃ e ∈ t, omega e = true} = 1 - ∏ e ∈ t, (1 - p e) := by
-- proof
  apply StatMech.Sharpness.abgr_probV_anyOpen p t

/--
[abgrMerge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgrMerge_mem_eq
  [Fintype E]
  [DecidableEq E]
  {s : Finset E}
-- given
  (gamma : {e // e ∈ s} -> Bool)
  (eta : {e // e ∉ s} -> Bool)
  (e : {e // e ∈ s}) :
-- imply
  abgrMerge s gamma eta e = gamma e := by
-- proof
  apply StatMech.Sharpness.abgrMerge_mem s gamma eta e

/--
[abgrMerge_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgrMerge_notMem_eq
  [Fintype E]
  [DecidableEq E]
  {s : Finset E}
-- given
  (gamma : {e // e ∈ s} -> Bool)
  (eta : {e // e ∉ s} -> Bool)
  (e : {e // e ∉ s}) :
-- imply
  abgrMerge s gamma eta e = eta e := by
-- proof
  apply StatMech.Sharpness.abgrMerge_notMem s gamma eta e

/--
[abgr_probV_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgr_probV_split_eq
  [Fintype E]
  [DecidableEq E]
  {s : Finset E}
  {q : Real}
  {A : Set (ConfigSpace E)}
-- given
  (p : E -> Real) :
-- imply
  probV (paramOn s q p) A = ∑ eta : {e // e ∉ s} -> Bool, (∏ e : {e // e ∉ s}, if eta e then p e else 1 - p e) * probV (fun _ : {e // e ∈ s} => q) {gamma | abgrMerge s gamma eta ∈ A} := by
-- proof
  apply StatMech.Sharpness.abgr_probV_split s q p A

/--
[abgrKeepGhost_chosen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgrKeepGhost_chosen_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V}
  {omega : ConfigSpace (Sym2 (Option V))} :
-- imply
  abgrKeepGhost x omega s(some x, none) = omega s(some x, none) := by
-- proof
  apply StatMech.Sharpness.abgrKeepGhost_chosen G x omega

/--
[abgrKeepGhost_physical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgrKeepGhost_physical_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x a b : V}
  {omega : ConfigSpace (Sym2 (Option V))} :
-- imply
  abgrKeepGhost x omega s(some a, some b) = omega s(some a, some b) := by
-- proof
  apply StatMech.Sharpness.abgrKeepGhost_physical G x a b omega

/--
[abgrKeepGhost_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgrKeepGhost_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V}
  {omega : ConfigSpace (Sym2 (Option V))} :
-- imply
  abgrKeepGhost x omega <= omega := by
-- proof
  apply StatMech.Sharpness.abgrKeepGhost_le G x omega

/--
[abgrCloseGhost_ghost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgrCloseGhost_ghost_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V}
  {omega : ConfigSpace (Sym2 (Option V))} :
-- imply
  abgrCloseGhost omega s(some x, none) = false := by
-- proof
  apply StatMech.Sharpness.abgrCloseGhost_ghost G x omega

/--
[abgrCloseGhost_physical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgrCloseGhost_physical_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b : V}
  {omega : ConfigSpace (Sym2 (Option V))} :
-- imply
  abgrCloseGhost omega s(some a, some b) = omega s(some a, some b) := by
-- proof
  apply StatMech.Sharpness.abgrCloseGhost_physical G a b omega

/--
[abgrCloseGhost_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgrCloseGhost_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {omega : ConfigSpace (Sym2 (Option V))} :
-- imply
  abgrCloseGhost omega <= omega := by
-- proof
  apply StatMech.Sharpness.abgrCloseGhost_le G omega

/--
[abgr_connEvent_iff_exists_keepGhost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgr_connEvent_iff_exists_keepGhost_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {omega : ConfigSpace (Sym2 (Option V))} :
-- imply
  omega ∈ connEvent (withGhost G) Set.univ (some o) {none} ↔ ∃ x : V, omega s(some x, none) = true ∧ abgrKeepGhost x omega ∈ connEvent (withGhost G) Set.univ (some o) {none} := by
-- proof
  apply StatMech.Sharpness.abgr_connEvent_iff_exists_keepGhost G o omega

/--
[abgr_connEvent_iff_exists_physical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgr_connEvent_iff_exists_physical_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {omega : ConfigSpace (Sym2 (Option V))} :
-- imply
  omega ∈ connEvent (withGhost G) Set.univ (some o) {none} ↔ ∃ x : V, omega s(some x, none) = true ∧ abgrCloseGhost omega ∈ connEvent (withGhost G) Set.univ (some o) {some x} := by
-- proof
  apply StatMech.Sharpness.abgr_connEvent_iff_exists_physical G o omega

/--
[abgr_connEvent_iff_exists_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgr_connEvent_iff_exists_active_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {omega : ConfigSpace (Sym2 (Option V))} :
-- imply
  omega ∈ connEvent (withGhost G) Set.univ (some o) {none} ↔ ∃ x ∈ abgrActive (G := G) o omega, omega s(some x, none) = true := by
-- proof
  apply StatMech.Sharpness.abgr_connEvent_iff_exists_active G o omega

/--
[abgrGhostEdgeEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgrGhostEdgeEquiv_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V} :
-- imply
  (abgrGhostEdgeEquiv (V := V) x : Sym2 (Option V)) = s(some x, none) := by
-- proof
  apply StatMech.Sharpness.abgrGhostEdgeEquiv_apply G x

/--
[abgrCloseGhost_merge_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgrCloseGhost_merge_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (gamma : {e // e ∈ FieldGhostDict.ghostEdges V} -> Bool)
  (eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool) :
-- imply
  abgrCloseGhost (abgrMerge (FieldGhostDict.ghostEdges V) gamma eta) = abgrMerge (FieldGhostDict.ghostEdges V) (fun _ => false) eta := by
-- proof
  apply StatMech.Sharpness.abgrCloseGhost_merge_eq G gamma eta

/--
[abgrActive_merge_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgrActive_merge_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (gamma : {e // e ∈ FieldGhostDict.ghostEdges V} -> Bool)
  (eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool) :
-- imply
  abgrActive (G := G) o (abgrMerge (FieldGhostDict.ghostEdges V) gamma eta) = abgrActive (G := G) o (abgrMerge (FieldGhostDict.ghostEdges V) (fun _ => false) eta) := by
-- proof
  apply StatMech.Sharpness.abgrActive_merge_eq G o gamma eta

/--
[abgr_section_iff_anyOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgr_section_iff_anyOpen_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (gamma : {e // e ∈ FieldGhostDict.ghostEdges V} -> Bool)
  (eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool) :
-- imply
  abgrMerge (FieldGhostDict.ghostEdges V) gamma eta ∈ connEvent (withGhost G) Set.univ (some o) {none} ↔ ∃ e ∈ abgrActiveGhost G o eta, gamma e = true := by
-- proof
  apply StatMech.Sharpness.abgr_section_iff_anyOpen G o gamma eta

/--
[abgr_abfaMag_eq_cluster_mixture](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgr_abfaMag_eq_cluster_mixture_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real) :
-- imply
  abfaMag G J o beta h = ∑ eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool, (∏ e : {e // e ∉ FieldGhostDict.ghostEdges V}, if eta e then pBeta (abfaLiftCoupling G J e) beta else 1 - pBeta (abfaLiftCoupling G J e) beta) * (1 - (1 - qField h) ^ (abgrActiveGhost G o eta).card) := by
-- proof
  apply StatMech.Sharpness.abgr_abfaMag_eq_cluster_mixture G J o beta h

/--
[abgr_sum_offWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgr_sum_offWeight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
-- given
  (J : Sym2 V -> Real) :
-- imply
  ∑ eta, abgrOffWeight G J beta eta = 1 := by
-- proof
  apply StatMech.Sharpness.abgr_sum_offWeight G J beta

/--
[abgr_offWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgr_offWeight_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
-- given
  (J : Sym2 V -> Real)
  (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e)
  (hbeta : 0 ≤ beta)
  (eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool) :
-- imply
  0 ≤ abgrOffWeight G J beta eta := by
-- proof
  apply StatMech.Sharpness.abgr_offWeight_nonneg G J beta hJ hbeta eta

/--
[abgr_cluster_profile_eq_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgr_cluster_profile_eq_exp_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {k : Nat}
-- given
  (h : Real) :
-- imply
  1 - (1 - qField h) ^ k = 1 - Real.exp (-(h * k)) := by
-- proof
  apply StatMech.Sharpness.abgr_cluster_profile_eq_exp G h k

/--
[abgr_hasDerivAt_abfaMag_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgr_hasDerivAt_abfaMag_field_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real) :
-- imply
  HasDerivAt (fun t => abfaMag G J o beta t) (∑ eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool, abgrOffWeight G J beta eta * ((abgrActiveGhost G o eta).card * Real.exp (-(h * (abgrActiveGhost G o eta).card)))) h := by
-- proof
  apply StatMech.Sharpness.abgr_hasDerivAt_abfaMag_field G J o beta h

/--
[abgr_hasDerivAt_deriv_abfaMag_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgr_hasDerivAt_deriv_abfaMag_field_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real) :
-- imply
  HasDerivAt (fun t => deriv (fun u => abfaMag G J o beta u) t) (-(∑ eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool, abgrOffWeight G J beta eta * (((abgrActiveGhost G o eta).card : Real) ^ 2 * Real.exp (-(h * (abgrActiveGhost G o eta).card))))) h := by
-- proof
  apply StatMech.Sharpness.abgr_hasDerivAt_deriv_abfaMag_field G J o beta h

/--
[abgr_nat_mul_exp_le_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgr_nat_mul_exp_le_inv_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {k : Nat}
-- given
  (h : Real)
  (hh : 0 < h) :
-- imply
  (k : Real) * Real.exp (-(h * k)) ≤ 1 / h := by
-- proof
  apply StatMech.Sharpness.abgr_nat_mul_exp_le_inv G h hh k

/--
[abgr_nat_sq_mul_exp_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgr_nat_sq_mul_exp_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {k : Nat}
-- given
  (h : Real)
  (hh : 0 < h) :
-- imply
  (k : Real) ^ 2 * Real.exp (-(h * k)) ≤ 2 / h ^ 2 := by
-- proof
  apply StatMech.Sharpness.abgr_nat_sq_mul_exp_le G h hh k

/--
[abgr_deriv_abfaMag_field_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgr_deriv_abfaMag_field_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (J : Sym2 V -> Real)
  (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e)
  (beta h : Real)
  (hbeta : 0 ≤ beta)
  (hh : 0 < h) :
-- imply
  deriv (fun t => abfaMag G J o beta t) h ≤ 1 / h := by
-- proof
  apply StatMech.Sharpness.abgr_deriv_abfaMag_field_le G J hJ o beta h hbeta hh

/--
[abgr_abs_deriv_deriv_abfaMag_field_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgr_abs_deriv_deriv_abfaMag_field_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (J : Sym2 V -> Real)
  (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e)
  (beta h : Real)
  (hbeta : 0 ≤ beta)
  (hh : 0 < h) :
-- imply
  |deriv (fun t => deriv (fun u => abfaMag G J o beta u) t) h| ≤ 2 / h ^ 2 := by
-- proof
  apply StatMech.Sharpness.abgr_abs_deriv_deriv_abfaMag_field_le G J hJ o beta h hbeta hh

/--
[abgr_taylor_remainder_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgr_taylor_remainder_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y K : Real}
-- given
  (f : Real -> Real)
  (hK : 0 <= K)
  (hfdiff : forall (z : Real), z ∈ Set.uIcc x y -> DifferentiableAt Real f z)
  (hf'diff : forall (z : Real), z ∈ Set.uIcc x y -> DifferentiableAt Real (fun t => deriv f t) z)
  (hf'bound : forall (z : Real), z ∈ Set.uIcc x y -> |deriv (fun t => deriv f t) z| <= K) :
-- imply
  |f y - f x - deriv f x * (y - x)| <= K * |y - x| ^ 2 := by
-- proof
  apply StatMech.Sharpness.abgr_taylor_remainder_le G f x y K hK hfdiff hf'diff hf'bound

/--
[abgr_hasDerivAt_limit_of_taylor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean)
-/
@[path]
private lemma abgr_hasDerivAt_limit_of_taylor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x r K : Real}
-- given
  (f : Nat -> Real -> Real)
  (g : Real -> Real)
  (d : Nat -> Real)
  (hr : 0 < r)
  (hK : 0 <= K)
  (hlim : forall y, |y - x| < r -> Tendsto (fun n => f n y) atTop (nhds (g y)))
  (htaylor : forall n y, |y - x| < r -> |f n y - f n x - d n * (y - x)| <= K * |y - x| ^ 2) :
-- imply
  exists L, HasDerivAt g L x := by
-- proof
  apply StatMech.Sharpness.abgr_hasDerivAt_limit_of_taylor G f g d x r K hr hK hlim htaylor


-- created on 2026-10-23
