import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.KramersWannierDuality
open Finset StatMech StatMech.Ising


/--
[cut_gen_eq_fiber_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierDuality.lean)
-/
@[path]
private lemma cut_gen_eq_fiber_sum_eq
  [Fintype V]
  [DecidableEq V]
  {t : ℝ} :
-- imply
  (∑ s : ConfigSpace V, t ^ (cutEdges Gp s).card) = ∑ δ ∈ cutSpace Gp, ((Finset.univ.filter (fun s : ConfigSpace V => cutEdges Gp s = δ)).card : ℝ) * t ^ δ.card := by
-- proof
  apply StatMech.Ising.cut_gen_eq_fiber_sum t

/--
[cut_gen_eq_mult](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierDuality.lean)
-/
@[path]
private lemma cut_gen_eq_mult_eq
  [Fintype V]
  [DecidableEq V]
  {t mult : ℝ}
-- given
  (hfib : ∀ δ ∈ cutSpace Gp, ((Finset.univ.filter (fun s : ConfigSpace V => cutEdges Gp s = δ)).card : ℝ) = mult) :
-- imply
  (∑ s : ConfigSpace V, t ^ (cutEdges Gp s).card) = mult * ∑ δ ∈ cutSpace Gp, t ^ δ.card := by
-- proof
  apply StatMech.Ising.cut_gen_eq_mult t mult hfib

/--
[mem_cutEdges_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierDuality.lean)
-/
@[path]
private lemma mem_cutEdges_iff_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V}
  {x y : V}
-- given
  (hadj : Gp.Adj x y) :
-- imply
  s(x, y) ∈ cutEdges Gp s ↔ s x ≠ s y := by
-- proof
  apply StatMech.Ising.mem_cutEdges_iff s hadj

/--
[agree_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierDuality.lean)
-/
@[path]
private lemma agree_adj_eq
  [Fintype V]
  [DecidableEq V]
  {s₁ s₂ : ConfigSpace V}
  {x y : V}
-- given
  (hcut : cutEdges Gp s₁ = cutEdges Gp s₂)
  (hadj : Gp.Adj x y) :
-- imply
  (s₁ x = s₂ x) ↔ (s₁ y = s₂ y) := by
-- proof
  apply StatMech.Ising.agree_adj hcut hadj

/--
[agree_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierDuality.lean)
-/
@[path]
private lemma agree_walk_eq
  [Fintype V]
  [DecidableEq V]
  {s₁ s₂ : ConfigSpace V}
  {x y : V}
  {w : Gp.Walk x y}
-- given
  (hcut : cutEdges Gp s₁ = cutEdges Gp s₂) :
-- imply
  (s₁ x = s₂ x) ↔ (s₁ y = s₂ y) := by
-- proof
  apply StatMech.Ising.agree_walk hcut w

/--
[eq_or_flip_of_cutEdges_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierDuality.lean)
-/
@[path]
private lemma eq_or_flip_of_cutEdges_eq_eq
  [Fintype V]
  [DecidableEq V]
  {s₁ s₂ : ConfigSpace V}
-- given
  (hG : Gp.Preconnected)
  (hcut : cutEdges Gp s₁ = cutEdges Gp s₂) :
-- imply
  s₂ = s₁ ∨ s₂ = (fun v => ! s₁ v) := by
-- proof
  apply StatMech.Ising.eq_or_flip_of_cutEdges_eq hG hcut

/--
[fiber_card_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierDuality.lean)
-/
@[path]
private lemma fiber_card_eq_two_eq
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {δ : Finset (Sym2 V)}
  {s : ConfigSpace V}
-- given
  (hG : Gp.Preconnected)
  (hs : cutEdges Gp s = δ) :
-- imply
  (Finset.univ.filter (fun s' : ConfigSpace V => cutEdges Gp s' = δ)).card = 2 := by
-- proof
  apply StatMech.Ising.fiber_card_eq_two hG hs

/--
[cutSpace_gen_eq_evenSubgraph_gen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierDuality.lean)
-/
@[path]
private lemma cutSpace_gen_eq_evenSubgraph_gen_eq
  [Fintype V]
  [DecidableEq V]
  {t : ℝ}
-- given
  (hhist : Multiset.map (fun S => S.card) (cutSpace Gp).val = Multiset.map (fun S => S.card) (evenSubgraphs Gd).val) :
-- imply
  (∑ δ ∈ cutSpace Gp, t ^ δ.card) = ∑ F ∈ evenSubgraphs Gd, t ^ F.card := by
-- proof
  apply StatMech.Ising.cutSpace_gen_eq_evenSubgraph_gen t hhist

/--
[cutEvenSubgraphMatching_of_hist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierDuality.lean)
-/
@[path]
private lemma cutEvenSubgraphMatching_of_hist_eq
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {t : ℝ}
-- given
  (hG : Gp.Preconnected)
  (hhist : Multiset.map (fun S => S.card) (cutSpace Gp).val = Multiset.map (fun S => S.card) (evenSubgraphs Gd).val) :
-- imply
  CutEvenSubgraphMatching Gp Gd t 2 := by
-- proof
  apply StatMech.Ising.cutEvenSubgraphMatching_of_hist hG t hhist

/--
[cutEdges_eq_cutEdgesB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierDuality.lean)
-/
@[path]
private lemma cutEdges_eq_cutEdgesB_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V} :
-- imply
  cutEdges G s = cutEdgesB G s := by
-- proof
  apply StatMech.Ising.cutEdges_eq_cutEdgesB s

/--
[cutSpace_eq_cutSpaceB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierDuality.lean)
-/
@[path]
private lemma cutSpace_eq_cutSpaceB_eq
  [Fintype V]
  [DecidableEq V] :
-- imply
  cutSpace G = cutSpaceB G := by
-- proof
  apply StatMech.Ising.cutSpace_eq_cutSpaceB

/--
[K4_preconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierDuality.lean)
-/
@[path]
private lemma K4_preconnected_eq :
-- imply
  (K4).Preconnected := by
-- proof
  apply StatMech.Ising.K4_preconnected

/--
[k4_cutSpace_evenSubgraph_hist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierDuality.lean)
-/
@[path]
private lemma k4_cutSpace_evenSubgraph_hist_eq :
-- imply
  Multiset.map (fun S => S.card) (cutSpaceB (K4)).val = Multiset.map (fun S => S.card) (evenSubgraphsB (K4)).val := by
-- proof
  apply StatMech.Ising.k4_cutSpace_evenSubgraph_hist

/--
[k4_cutEvenSubgraphMatching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierDuality.lean)
-/
@[path]
private lemma k4_cutEvenSubgraphMatching_eq
  {t : ℝ} :
-- imply
  CutEvenSubgraphMatching (K4) (K4) t 2 := by
-- proof
  apply StatMech.Ising.k4_cutEvenSubgraphMatching t

/--
[isingZ_self_dual_K4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierDuality.lean)
-/
@[path]
private lemma isingZ_self_dual_K4_eq
  {β βstar : ℝ}
-- given
  (htemp : Real.tanh βstar = Real.exp (-2 * β)) :
-- imply
  isingZ (K4) βstar 0 = ((2 : ℝ) ^ Fintype.card (Fin 4) * (Real.cosh βstar) ^ (K4).edgeFinset.card / (Real.exp (β * (K4).edgeFinset.card) * 2)) * isingZ (K4) β 0 := by
-- proof
  apply StatMech.Ising.isingZ_self_dual_K4 β βstar htemp


-- created on 2026-10-23
