import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierGeneral.Part5
open Finset SimpleGraph StatMech StatMech.Ising


/--
[walkDis_parity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean)
-/
@[path]
private lemma walkDis_parity_eq
  {Gp : SimpleGraph V}
  {s : ConfigSpace V}
  {x y : V}
  {p : Gp.Walk x y} :
-- imply
  walkDis Gp s p % 2 = (if s x ≠ s y then 1 else 0) := by
-- proof
  apply StatMech.Ising.walkDis_parity Gp s p

/--
[walkDis_closed_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean)
-/
@[path]
private lemma walkDis_closed_even_eq
  {Gp : SimpleGraph V}
  {s : ConfigSpace V}
  {x : V}
  {p : Gp.Walk x x} :
-- imply
  walkDis Gp s p % 2 = 0 := by
-- proof
  apply StatMech.Ising.walkDis_closed_even Gp s p

/--
[walkDis_eq_darts_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean)
-/
@[path]
private lemma walkDis_eq_darts_sum_eq
  {Gp : SimpleGraph V}
  {s : ConfigSpace V}
  {x y : V}
  {p : Gp.Walk x y} :
-- imply
  walkDis Gp s p = (p.darts.map (fun d => if s d.fst ≠ s d.snd then 1 else 0)).sum := by
-- proof
  apply StatMech.Ising.walkDis_eq_darts_sum Gp s p

/--
[cutSpace_subset_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean)
-/
@[path]
private lemma cutSpace_subset_edgeFinset_eq
  [Fintype V]
  [DecidableEq V]
  {Gp Gd}
  {δ : Finset (Sym2 V)}
-- given
  (hδ : δ ∈ cutSpace Gp) :
-- imply
  δ ⊆ Gp.edgeFinset := by
-- proof
  apply StatMech.Ising.cutSpace_subset_edgeFinset hδ

/--
[EdgeCrossing.image_mem_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean)
-/
@[path]
private lemma image_mem_even_eq
  [Fintype V]
  [DecidableEq V]
  {Gp Gd}
  {Φ : EdgeCrossing Gp Gd}
  {δ : Finset (Sym2 V)}
-- given
  (hδ : δ ∈ cutSpace Gp) :
-- imply
  δ.image Φ.ψ ∈ evenSubgraphs Gd := by
-- proof
  apply StatMech.Ising.EdgeCrossing.image_mem_even Φ hδ

/--
[EdgeCrossing.invImage_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean)
-/
@[path]
private lemma invImage_image_eq
  [Fintype V]
  [DecidableEq V]
  {Gp Gd}
  {Φ : EdgeCrossing Gp Gd}
  {δ : Finset (Sym2 V)} :
-- imply
  (δ.image Φ.ψ).image Φ.ψ.symm = δ := by
-- proof
  apply StatMech.Ising.EdgeCrossing.invImage_image Φ δ

/--
[EdgeCrossing.image_invImage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean)
-/
@[path]
private lemma image_invImage_eq
  [Fintype V]
  [DecidableEq V]
  {Gp Gd}
  {Φ : EdgeCrossing Gp Gd}
  {F : Finset (Sym2 V)} :
-- imply
  (F.image Φ.ψ.symm).image Φ.ψ = F := by
-- proof
  apply StatMech.Ising.EdgeCrossing.image_invImage Φ F

/--
[EdgeCrossing.card_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean)
-/
@[path]
private lemma card_image_eq
  [Fintype V]
  [DecidableEq V]
  {Gp Gd}
  {Φ : EdgeCrossing Gp Gd}
  {δ : Finset (Sym2 V)} :
-- imply
  (δ.image Φ.ψ).card = δ.card := by
-- proof
  apply StatMech.Ising.EdgeCrossing.card_image Φ δ

/--
[EdgeCrossing.hist_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean)
-/
@[path]
private lemma hist_eq_eq
  [Fintype V]
  [DecidableEq V]
  {Gp Gd}
  {Φ : EdgeCrossing Gp Gd} :
-- imply
  Multiset.map (fun S => S.card) (cutSpace Gp).val = Multiset.map (fun S => S.card) (evenSubgraphs Gd).val := by
-- proof
  apply StatMech.Ising.EdgeCrossing.hist_eq Φ

/--
[cutMatching_of_edgeCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean)
-/
@[path]
private lemma cutMatching_of_edgeCrossing_eq
  [Fintype V]
  [DecidableEq V]
  {Gp Gd}
  [Nonempty V]
  {Φ : EdgeCrossing Gp Gd}
  {t : ℝ}
-- given
  (hG : Gp.Preconnected) :
-- imply
  CutEvenSubgraphMatching Gp Gd t 2 := by
-- proof
  apply StatMech.Ising.cutMatching_of_edgeCrossing hG Φ t

/--
[isingZ_self_dual_of_edgeCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean)
-/
@[path]
private lemma isingZ_self_dual_of_edgeCrossing_eq
  [Fintype V]
  [DecidableEq V]
  {Gp Gd}
  [Nonempty V]
  {Φ : EdgeCrossing Gp Gd}
  {β βstar : ℝ}
-- given
  (hG : Gp.Preconnected)
  (htemp : Real.tanh βstar = Real.exp (-2 * β)) :
-- imply
  isingZ Gd βstar 0 = ((2 : ℝ) ^ Fintype.card V * (Real.cosh βstar) ^ Gd.edgeFinset.card / (Real.exp (β * Gp.edgeFinset.card) * 2)) * isingZ Gp β 0 := by
-- proof
  apply StatMech.Ising.isingZ_self_dual_of_edgeCrossing hG Φ β βstar htemp

/--
[incCount_image_eq_filter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean)
-/
@[path]
private lemma incCount_image_eq_filter_eq
  [Fintype V]
  [DecidableEq V]
  {Gp Gd}
  {ψ : Sym2 V ≃ Sym2 V}
  {δ : Finset (Sym2 V)}
  {w : V} :
-- imply
  incCount (δ.image ψ) w = (δ.filter (fun e => w ∈ ψ e)).card := by
-- proof
  apply StatMech.Ising.incCount_image_eq_filter ψ δ w

/--
[cut_to_even_of_faceWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean)
-/
@[path]
private lemma cut_to_even_of_faceWalk_eq
  [Fintype V]
  [DecidableEq V]
  {Gp Gd}
  {ψ : Sym2 V ≃ Sym2 V}
  {basePt : V → V}
  {faceWalk : (w : V) → Gp.Walk (basePt w) (basePt w)}
-- given
  (hbridge : ∀ (s : ConfigSpace V) (w : V), incCount ((cutEdges Gp s).image ψ) w = walkDis Gp s (faceWalk w)) :
-- imply
  ∀ δ ∈ cutSpace Gp, IsEvenSubgraph (δ.image ψ) := by
-- proof
  apply StatMech.Ising.cut_to_even_of_faceWalk ψ faceWalk hbridge

/--
[k4Comp_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean)
-/
@[path]
private lemma k4Comp_involutive_eq
  {e : Sym2 (Fin 4)} :
-- imply
  k4Comp (k4Comp e) = e := by
-- proof
  apply StatMech.Ising.k4Comp_involutive e

/--
[k4CompEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean)
-/
@[path]
private lemma k4CompEquiv_apply_eq
  {e : Sym2 (Fin 4)} :
-- imply
  k4CompEquiv e = k4Comp e := by
-- proof
  apply StatMech.Ising.k4CompEquiv_apply e

/--
[k4CompEquiv_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean)
-/
@[path]
private lemma k4CompEquiv_symm_apply_eq
  {e : Sym2 (Fin 4)} :
-- imply
  k4CompEquiv.symm e = k4Comp e := by
-- proof
  apply StatMech.Ising.k4CompEquiv_symm_apply e

/--
[mem_K4_edgeFinset_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean)
-/
@[path]
private lemma mem_K4_edgeFinset_iff_eq
  {e : Sym2 (Fin 4)} :
-- imply
  e ∈ (K4).edgeFinset ↔ ¬ e.IsDiag := by
-- proof
  apply StatMech.Ising.mem_K4_edgeFinset_iff e

/--
[k4Comp_not_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean)
-/
@[path]
private lemma k4Comp_not_diag_eq
  {e : Sym2 (Fin 4)}
-- given
  (he : ¬ e.IsDiag) :
-- imply
  ¬ (k4Comp e).IsDiag := by
-- proof
  apply StatMech.Ising.k4Comp_not_diag e he

/--
[k4Comp_cut_to_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean)
-/
@[path]
private lemma k4Comp_cut_to_even_eq :
-- imply
  ∀ δ ∈ cutSpaceB (K4), IsEvenSubgraph (δ.image k4Comp) := by
-- proof
  apply StatMech.Ising.k4Comp_cut_to_even

/--
[k4Comp_even_to_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean)
-/
@[path]
private lemma k4Comp_even_to_cut_eq :
-- imply
  ∀ F ∈ evenSubgraphsB (K4), (F.image k4Comp) ∈ cutSpaceB (K4) := by
-- proof
  apply StatMech.Ising.k4Comp_even_to_cut

/--
[isingZ_self_dual_K4_via_framework](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean)
-/
@[path]
private lemma isingZ_self_dual_K4_via_framework_eq
  {β βstar : ℝ}
-- given
  (htemp : Real.tanh βstar = Real.exp (-2 * β)) :
-- imply
  isingZ (K4) βstar 0 = ((2 : ℝ) ^ Fintype.card (Fin 4) * (Real.cosh βstar) ^ (K4).edgeFinset.card / (Real.exp (β * (K4).edgeFinset.card) * 2)) * isingZ (K4) β 0 := by
-- proof
  apply StatMech.Ising.isingZ_self_dual_K4_via_framework β βstar htemp


-- created on 2026-10-23
