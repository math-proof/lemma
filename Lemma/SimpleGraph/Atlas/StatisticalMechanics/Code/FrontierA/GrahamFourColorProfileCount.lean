import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorProfileCount.Part3
open Finset Classical StatMech StatMech.FrontierA


/--
[grahamFourColor_perFiber_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorProfileCount.lean)
-/
@[path]
private lemma grahamFourColor_perFiber_count_eq
  {alpha : Type*}
  [Fintype alpha]
  [DecidableEq alpha]
  {n k1 k2 k3 : Nat}
-- given
  (hn : Fintype.card alpha = n) :
-- imply
  #((Finset.univ : Finset (GrahamFourColoring alpha)).filter (fun c => c.IsPartition Finset.univ /\ #c.color1 = k1 /\ #c.color2 = k2 /\ #c.color3 = k3)) = n.choose k1 * (n - k1).choose k2 * (n - k1 - k2).choose k3 := by
-- proof
  apply StatMech.FrontierA.grahamFourColor_perFiber_count alpha n k1 k2 k3 hn

/--
[graham_mem_sigmaFinsetEquivPi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorProfileCount.lean)
-/
@[path]
private lemma graham_mem_sigmaFinsetEquivPi_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {x : gamma e}
-- given
  (S : Finset (Sigma fun e : E => gamma e)) :
-- imply
  x ∈ sigmaFinsetEquivPi S e <-> (Sigma.mk e x : Sigma fun e : E => gamma e) ∈ S := by
-- proof
  apply StatMech.FrontierA.graham_mem_sigmaFinsetEquivPi S e x

/--
[graham_disjoint_fiberwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorProfileCount.lean)
-/
@[path]
private lemma graham_disjoint_fiberwise_eq
  [Fintype E]
  [DecidableEq E]
-- given
  (S T : Finset (Sigma fun e : E => gamma e)) :
-- imply
  Disjoint S T <-> forall e, Disjoint (sigmaFinsetEquivPi S e) (sigmaFinsetEquivPi T e) := by
-- proof
  apply StatMech.FrontierA.graham_disjoint_fiberwise S T

/--
[grahamFourColor_partition_fiberwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorProfileCount.lean)
-/
@[path]
private lemma grahamFourColor_partition_fiberwise_eq
  [Fintype E]
  [DecidableEq E]
-- given
  (c : GrahamFourColoring (Sigma fun e : E => gamma e)) :
-- imply
  c.IsPartition Finset.univ <-> forall e, (grahamFourColorSigmaEquivPi c e).IsPartition Finset.univ := by
-- proof
  apply StatMech.FrontierA.grahamFourColor_partition_fiberwise c

/--
[grahamFourColor_pi_profile_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorProfileCount.lean)
-/
@[path]
private lemma grahamFourColor_pi_profile_count_eq
  [Fintype E]
  [DecidableEq E]
-- given
  (K1 K2 K3 : E -> Nat) :
-- imply
  #((Finset.univ : Finset (GrahamFourColoring (Sigma fun e : E => gamma e))).filter (fun c => c.IsPartition Finset.univ /\ grahamFourColorProfile c = (K1, K2, K3))) = ∏ e : E, (Fintype.card (gamma e)).choose (K1 e) * (Fintype.card (gamma e) - K1 e).choose (K2 e) * (Fintype.card (gamma e) - K1 e - K2 e).choose (K3 e) := by
-- proof
  apply StatMech.FrontierA.grahamFourColor_pi_profile_count K1 K2 K3

/--
[grahamFourColor_edgecopy_profile_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorProfileCount.lean)
-/
@[path]
private lemma grahamFourColor_edgecopy_profile_count_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (total a b c : G.edgeFinset -> Nat) :
-- imply
  #((grahamFourColorings (Finset.univ : Finset (Copy G total))).filter (fun q => profileFlux G total q.color1 = a /\ profileFlux G total q.color2 = b /\ profileFlux G total q.color3 = c)) = ∏ e : G.edgeFinset, (total e).choose (a e) * (total e - a e).choose (b e) * (total e - a e - b e).choose (c e) := by
-- proof
  apply StatMech.FrontierA.grahamFourColor_edgecopy_profile_count total a b c

/--
[grahamFourColor_profile_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorProfileCount.lean)
-/
@[path]
private lemma grahamFourColor_profile_sum_le_eq
  [Fintype V]
  [DecidableEq V]
  {q : GrahamFourColoring (Copy G total)}
-- given
  (total : G.edgeFinset -> Nat)
  (hq : q.IsPartition Finset.univ) :
-- imply
  forall e, profileFlux G total q.color1 e + profileFlux G total q.color2 e + profileFlux G total q.color3 e <= total e := by
-- proof
  apply StatMech.FrontierA.grahamFourColor_profile_sum_le total q hq

/--
[graham_profileFlux_union_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorProfileCount.lean)
-/
@[path]
private lemma graham_profileFlux_union_disjoint_eq
  [Fintype V]
  [DecidableEq V]
  {S T : Finset (Copy G total)}
-- given
  (total : G.edgeFinset -> Nat)
  (hST : Disjoint S T) :
-- imply
  profileFlux G total (S ∪ T) = fun e => profileFlux G total S e + profileFlux G total T e := by
-- proof
  apply StatMech.FrontierA.graham_profileFlux_union_disjoint total S T hST

/--
[grahamFourColor_profile_color4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorProfileCount.lean)
-/
@[path]
private lemma grahamFourColor_profile_color4_eq
  [Fintype V]
  [DecidableEq V]
  {q : GrahamFourColoring (Copy G total)}
-- given
  (total : G.edgeFinset -> Nat)
  (hq : q.IsPartition Finset.univ) :
-- imply
  profileFlux G total (q.color4 Finset.univ) = fun e => total e - profileFlux G total q.color1 e - profileFlux G total q.color2 e - profileFlux G total q.color3 e := by
-- proof
  apply StatMech.FrontierA.grahamFourColor_profile_color4 total q hq


-- created on 2026-10-23
