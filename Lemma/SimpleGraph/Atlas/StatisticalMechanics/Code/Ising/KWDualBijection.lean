import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.KWDualBijection.Part2
open Finset SimpleGraph StatMech StatMech.Ising


/--
[incCount_symmDiff_mod_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWDualBijection.lean)
-/
@[path]
private lemma incCount_symmDiff_mod_two_eq
  [DecidableEq V]
  {A B : Finset (Sym2 V)}
  {v : V} :
-- imply
  incCount (symmDiff A B) v % 2 = (incCount A v + incCount B v) % 2 := by
-- proof
  apply StatMech.Ising.incCount_symmDiff_mod_two A B v

/--
[isEvenSubgraph_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWDualBijection.lean)
-/
@[path]
private lemma isEvenSubgraph_empty_eq
  [DecidableEq V] :
-- imply
  IsEvenSubgraph (∅ : Finset (Sym2 V)) := by
-- proof
  apply StatMech.Ising.isEvenSubgraph_empty

/--
[isEvenSubgraph_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWDualBijection.lean)
-/
@[path]
private lemma isEvenSubgraph_symmDiff_eq
  [DecidableEq V]
  {A B : Finset (Sym2 V)}
-- given
  (hA : IsEvenSubgraph A)
  (hB : IsEvenSubgraph B) :
-- imply
  IsEvenSubgraph (symmDiff A B) := by
-- proof
  apply StatMech.Ising.isEvenSubgraph_symmDiff hA hB

/--
[sym2map_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWDualBijection.lean)
-/
@[path]
private lemma sym2map_injective_eq
  [DecidableEq V]
  [DecidableEq W]
  {e : V ≃ W} :
-- imply
  Function.Injective (Sym2.map e) := by
-- proof
  apply StatMech.Ising.sym2map_injective e

/--
[card_transportEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWDualBijection.lean)
-/
@[path]
private lemma card_transportEdges_eq
  [DecidableEq V]
  [DecidableEq W]
  {e : V ≃ W}
  {F : Finset (Sym2 V)} :
-- imply
  (transportEdges e F).card = F.card := by
-- proof
  apply StatMech.Ising.card_transportEdges e F

/--
[incCount_transportEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWDualBijection.lean)
-/
@[path]
private lemma incCount_transportEdges_eq
  [DecidableEq V]
  [DecidableEq W]
  {e : V ≃ W}
  {F : Finset (Sym2 V)}
  {v : V} :
-- imply
  incCount (transportEdges e F) (e v) = incCount F v := by
-- proof
  apply StatMech.Ising.incCount_transportEdges e F v

/--
[isEvenSubgraph_transportEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWDualBijection.lean)
-/
@[path]
private lemma isEvenSubgraph_transportEdges_eq
  [DecidableEq V]
  [DecidableEq W]
  {e : V ≃ W}
  {F : Finset (Sym2 V)}
-- given
  (hF : IsEvenSubgraph F) :
-- imply
  IsEvenSubgraph (transportEdges e F) := by
-- proof
  apply StatMech.Ising.isEvenSubgraph_transportEdges e hF

/--
[transportEdges_symm_transportEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWDualBijection.lean)
-/
@[path]
private lemma transportEdges_symm_transportEdges_eq
  [DecidableEq V]
  [DecidableEq W]
  {e : V ≃ W}
  {F : Finset (Sym2 V)} :
-- imply
  transportEdges e.symm (transportEdges e F) = F := by
-- proof
  apply StatMech.Ising.transportEdges_symm_transportEdges e F

/--
[transportEdges_transportEdges_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWDualBijection.lean)
-/
@[path]
private lemma transportEdges_transportEdges_symm_eq
  [DecidableEq V]
  [DecidableEq W]
  {e : V ≃ W}
  {F : Finset (Sym2 W)} :
-- imply
  transportEdges e (transportEdges e.symm F) = F := by
-- proof
  apply StatMech.Ising.transportEdges_transportEdges_symm e F

/--
[transportEdges_subset_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWDualBijection.lean)
-/
@[path]
private lemma transportEdges_subset_edgeFinset_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {φ : G1 ≃g G2}
  {F : Finset (Sym2 V)}
-- given
  (hF : F ⊆ G1.edgeFinset) :
-- imply
  transportEdges φ.toEquiv F ⊆ G2.edgeFinset := by
-- proof
  apply StatMech.Ising.transportEdges_subset_edgeFinset φ hF

/--
[transportEdges_mem_evenPowerset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWDualBijection.lean)
-/
@[path]
private lemma transportEdges_mem_evenPowerset_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {φ : G1 ≃g G2}
  {F : Finset (Sym2 V)}
-- given
  (hF : F ∈ G1.edgeFinset.powerset.filter IsEvenSubgraph) :
-- imply
  transportEdges φ.toEquiv F ∈ G2.edgeFinset.powerset.filter IsEvenSubgraph := by
-- proof
  apply StatMech.Ising.transportEdges_mem_evenPowerset φ hF

/--
[evenSubgraph_tanh_sum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWDualBijection.lean)
-/
@[path]
private lemma evenSubgraph_tanh_sum_eq_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {φ : G1 ≃g G2}
  {t : ℝ} :
-- imply
  (∑ F ∈ G2.edgeFinset.powerset.filter IsEvenSubgraph, t ^ F.card) = ∑ F ∈ G1.edgeFinset.powerset.filter IsEvenSubgraph, t ^ F.card := by
-- proof
  apply StatMech.Ising.evenSubgraph_tanh_sum_eq φ t

/--
[dualContourMatching_of_iso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWDualBijection.lean)
-/
@[path]
private lemma dualContourMatching_of_iso_eq
  [Fintype V]
  [DecidableEq V]
  {φ : Gp ≃g Gd}
  {β βstar c : ℝ}
-- given
  (htemp : Real.tanh βstar = Real.exp (-2 * β))
  (hscalar : (2 : ℝ) ^ Fintype.card V * (Real.cosh βstar) ^ Gd.edgeFinset.card * ∑ F ∈ Gp.edgeFinset.powerset.filter IsEvenSubgraph, (Real.tanh βstar) ^ F.card = c * isingZ Gp β 0) :
-- imply
  DualContourMatching Gp Gd β βstar c := by
-- proof
  apply StatMech.Ising.dualContourMatching_of_iso φ β βstar c htemp hscalar

/--
[isingZ_self_dual_of_cycleSpace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWDualBijection.lean)
-/
@[path]
private lemma isingZ_self_dual_of_cycleSpace_eq
  [Fintype V]
  [DecidableEq V]
  {φ : Gp ≃g Gd}
  {β βstar c : ℝ}
-- given
  (htemp : Real.tanh βstar = Real.exp (-2 * β))
  (hscalar : (2 : ℝ) ^ Fintype.card V * (Real.cosh βstar) ^ Gd.edgeFinset.card * ∑ F ∈ Gp.edgeFinset.powerset.filter IsEvenSubgraph, (Real.tanh βstar) ^ F.card = c * isingZ Gp β 0) :
-- imply
  isingZ Gd βstar 0 = c * isingZ Gp β 0 := by
-- proof
  apply StatMech.Ising.isingZ_self_dual_of_cycleSpace φ β βstar c htemp hscalar

/--
[selfDual_evenSubgraph_tanh_sum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWDualBijection.lean)
-/
@[path]
private lemma selfDual_evenSubgraph_tanh_sum_eq_eq
  [Fintype V]
  [DecidableEq V]
  {φ : Gp ≃g Gd}
  {t : ℝ} :
-- imply
  (∑ F ∈ Gd.edgeFinset.powerset.filter IsEvenSubgraph, t ^ F.card) = ∑ F ∈ Gp.edgeFinset.powerset.filter IsEvenSubgraph, t ^ F.card := by
-- proof
  apply StatMech.Ising.selfDual_evenSubgraph_tanh_sum_eq φ t


-- created on 2026-10-23
