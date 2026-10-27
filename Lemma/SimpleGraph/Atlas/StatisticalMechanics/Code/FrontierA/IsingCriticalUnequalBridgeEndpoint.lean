import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeEndpoint
open StatMech StatMech.FrontierA


/--
[unequalReplicaExp2_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeEndpoint.lean)
-/
@[path]
private lemma unequalReplicaExp2_factor_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
  {J : Real}
-- given
  (hf : V -> Real)
  (hg : W -> Real)
  (f : ConfigSpace V -> Real)
  (g : ConfigSpace W -> Real) :
-- imply
  unequalReplicaExp2 G H J hf hg (fun a b => f a * g b) = expJ G.edgeFinset (fun _ => J) hf f * expJ H.edgeFinset (fun _ => J) hg g := by
-- proof
  apply StatMech.FrontierA.unequalReplicaExp2_factor G H J hf hg f g

/--
[unequalReplicaExp2_crossBond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeEndpoint.lean)
-/
@[path]
private lemma unequalReplicaExp2_crossBond_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
  {J : Real}
  {x : V}
  {y : W}
-- given
  (hf : V -> Real)
  (hg : W -> Real) :
-- imply
  unequalReplicaExp2 G H J hf hg (fun a b => bond (isingSumConfigEquiv.symm (a, b)) s(Sum.inl x, Sum.inr y)) = expJ G.edgeFinset (fun _ => J) hf (fun a => spin a x) * expJ H.edgeFinset (fun _ => J) hg (fun b => spin b y) := by
-- proof
  apply StatMech.FrontierA.unequalReplicaExp2_crossBond G H J hf hg x y

/--
[unequalReplicaExp2_finset_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeEndpoint.lean)
-/
@[path]
private lemma unequalReplicaExp2_finset_sum_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
  {J : Real}
  {S : Finset I}
-- given
  (hf : V -> Real)
  (hg : W -> Real)
  (F : I -> ConfigSpace V -> ConfigSpace W -> Real) :
-- imply
  unequalReplicaExp2 G H J hf hg (fun a b => ∑ i ∈ S, F i a b) = ∑ i ∈ S, unequalReplicaExp2 G H J hf hg (F i) := by
-- proof
  apply StatMech.FrontierA.unequalReplicaExp2_finset_sum G H J hf hg S F

/--
[unequalReplicaBridgeMoment_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeEndpoint.lean)
-/
@[path]
private lemma unequalReplicaBridgeMoment_zero_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
  {K : SimpleGraph (V ⊕ W)}
  [DecidableRel K.Adj]
  {J : Real}
-- given
  (hf : V -> Real)
  (hg : W -> Real) :
-- imply
  unequalReplicaBridgeMoment G H K J hf hg 0 = 1 := by
-- proof
  apply StatMech.FrontierA.unequalReplicaBridgeMoment_zero G H K J hf hg

/--
[unequalReplicaBridgeMean_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeEndpoint.lean)
-/
@[path]
private lemma unequalReplicaBridgeMean_zero_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
  {K : SimpleGraph (V ⊕ W)}
  [DecidableRel K.Adj]
  {J : Real}
-- given
  (hf : V -> Real)
  (hg : W -> Real) :
-- imply
  unequalReplicaBridgeMean G H K J hf hg 0 = unequalReplicaExp2 G H J hf hg (unequalReplicaBridgeInteraction G H K) := by
-- proof
  apply StatMech.FrontierA.unequalReplicaBridgeMean_zero G H K J hf hg

/--
[unequalReplicaBridgeMean_zero_eq_sum_interface](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeEndpoint.lean)
-/
@[path]
private lemma unequalReplicaBridgeMean_zero_eq_sum_interface_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
  {K : SimpleGraph (V ⊕ W)}
  [DecidableRel K.Adj]
  {J : Real}
-- given
  (hf : V -> Real)
  (hg : W -> Real) :
-- imply
  unequalReplicaBridgeMean G H K J hf hg 0 = ∑ e ∈ StatMech.FK.fis_interface G H K, unequalReplicaExp2 G H J hf hg (fun a b => bond (isingSumConfigEquiv.symm (a, b)) e) := by
-- proof
  apply StatMech.FrontierA.unequalReplicaBridgeMean_zero_eq_sum_interface G H K J hf hg


-- created on 2026-10-23
