import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierEvenToCut.Part8
open Finset SimpleGraph StatMech StatMech.Ising


/--
[walkParity_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean)
-/
@[path]
private lemma walkParity_nil_eq
  [DecidableEq V]
  {Gp : SimpleGraph V}
  {δ : Finset (Sym2 V)}
  {x : V} :
-- imply
  walkParity Gp δ (.nil : Gp.Walk x x) = false := by
-- proof
  apply StatMech.Ising.walkParity_nil Gp δ

/--
[walkParity_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean)
-/
@[path]
private lemma walkParity_cons_eq
  [DecidableEq V]
  {Gp : SimpleGraph V}
  {δ : Finset (Sym2 V)}
  {u v w : V}
  {p : Gp.Walk v w}
-- given
  (h : Gp.Adj u v) :
-- imply
  walkParity Gp δ (.cons h p) = (decide (s(u, v) ∈ δ)).xor (walkParity Gp δ p) := by
-- proof
  apply StatMech.Ising.walkParity_cons Gp δ h p

/--
[walkParity_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean)
-/
@[path]
private lemma walkParity_append_eq
  [DecidableEq V]
  {Gp : SimpleGraph V}
  {δ : Finset (Sym2 V)}
  {Gp δ}
  {x y z : V}
  {p : Gp.Walk x y}
  {q : Gp.Walk y z} :
-- imply
  walkParity Gp δ (p.append q) = (walkParity Gp δ p).xor (walkParity Gp δ q) := by
-- proof
  apply StatMech.Ising.walkParity_append Gp δ p q

/--
[walkParity_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean)
-/
@[path]
private lemma walkParity_reverse_eq
  [DecidableEq V]
  {Gp : SimpleGraph V}
  {δ : Finset (Sym2 V)}
  {Gp δ}
  {x y : V}
  {p : Gp.Walk x y} :
-- imply
  walkParity Gp δ p.reverse = walkParity Gp δ p := by
-- proof
  apply StatMech.Ising.walkParity_reverse Gp δ p

/--
[walkParity_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean)
-/
@[path]
private lemma walkParity_singleton_eq
  [DecidableEq V]
  {Gp : SimpleGraph V}
  {δ : Finset (Sym2 V)}
  {Gp δ}
  {x y : V}
-- given
  (h : Gp.Adj x y) :
-- imply
  walkParity Gp δ (SimpleGraph.Walk.cons h (.nil : Gp.Walk y y)) = decide (s(x, y) ∈ δ) := by
-- proof
  apply StatMech.Ising.walkParity_singleton Gp δ h

/--
[walkParity_eq_of_evenOnCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean)
-/
@[path]
private lemma walkParity_eq_of_evenOnCycles_eq
  [Fintype V]
  [DecidableEq V]
  {Gp δ}
  {x y : V}
  {p q : Gp.Walk x y}
-- given
  (hev : EvenOnCycles Gp δ) :
-- imply
  walkParity Gp δ p = walkParity Gp δ q := by
-- proof
  apply StatMech.Ising.walkParity_eq_of_evenOnCycles hev p q

/--
[parityConfig_adj_xor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean)
-/
@[path]
private lemma parityConfig_adj_xor_eq
  [Fintype V]
  [DecidableEq V]
  {Gp δ}
  (Gp δ)
  {v₀ : V}
  {x y : V}
-- given
  (hev : EvenOnCycles Gp δ)
  (hG : Gp.Preconnected)
  (h : Gp.Adj x y) :
-- imply
  (parityConfig Gp δ hG v₀ x).xor (parityConfig Gp δ hG v₀ y) = decide (s(x, y) ∈ δ) := by
-- proof
  apply StatMech.Ising.parityConfig_adj_xor hev hG v₀ h

/--
[cutEdges_parityConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean)
-/
@[path]
private lemma cutEdges_parityConfig_eq
  [Fintype V]
  [DecidableEq V]
  {Gp δ}
  (Gp δ)
  {v₀ : V}
-- given
  (hev : EvenOnCycles Gp δ)
  (hG : Gp.Preconnected)
  (hδ : δ ⊆ Gp.edgeFinset) :
-- imply
  cutEdges Gp (parityConfig Gp δ hG v₀) = δ := by
-- proof
  apply StatMech.Ising.cutEdges_parityConfig hev hG v₀ hδ

/--
[mem_cutSpace_of_evenOnCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean)
-/
@[path]
private lemma mem_cutSpace_of_evenOnCycles_eq
  [Fintype V]
  [DecidableEq V]
  {Gp δ}
  (Gp δ)
  [Nonempty V]
-- given
  (hG : Gp.Preconnected)
  (hδ : δ ⊆ Gp.edgeFinset)
  (hev : EvenOnCycles Gp δ) :
-- imply
  δ ∈ cutSpace Gp := by
-- proof
  apply StatMech.Ising.mem_cutSpace_of_evenOnCycles hG hδ hev

/--
[mem_image_symm_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean)
-/
@[path]
private lemma mem_image_symm_iff_eq
  [Fintype V]
  [DecidableEq V]
  {ψ : Sym2 V ≃ Sym2 V}
  {F : Finset (Sym2 V)}
  {e : Sym2 V} :
-- imply
  e ∈ F.image ψ.symm ↔ ψ e ∈ F := by
-- proof
  apply StatMech.Ising.mem_image_symm_iff ψ F e

/--
[walkParity_image_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean)
-/
@[path]
private lemma walkParity_image_symm_eq
  [Fintype V]
  [DecidableEq V]
  {ψ : Sym2 V ≃ Sym2 V}
  {F : Finset (Sym2 V)}
  {x y : V}
  {p : Gp.Walk x y} :
-- imply
  walkParity Gp (F.image ψ.symm) p = (p.darts.map (fun d => decide (ψ s(d.fst, d.snd) ∈ F))).foldr Bool.xor false := by
-- proof
  apply StatMech.Ising.walkParity_image_symm ψ F p

/--
[image_symm_subset_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean)
-/
@[path]
private lemma image_symm_subset_edgeFinset_eq
  [Fintype V]
  [DecidableEq V]
  {ψ : Sym2 V ≃ Sym2 V}
  {F : Finset (Sym2 V)}
-- given
  (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
  (hF : F ⊆ Gd.edgeFinset) :
-- imply
  F.image ψ.symm ⊆ Gp.edgeFinset := by
-- proof
  apply StatMech.Ising.image_symm_subset_edgeFinset ψ hsymm hF

/--
[even_to_cut_of_cycleParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean)
-/
@[path]
private lemma even_to_cut_of_cycleParity_eq
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {ψ : Sym2 V ≃ Sym2 V}
-- given
  (hG : Gp.Preconnected)
  (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
  (hcyc : ∀ F ∈ evenSubgraphs Gd, CycleParityCompatible Gp ψ F) :
-- imply
  ∀ F ∈ evenSubgraphs Gd, (F.image ψ.symm) ∈ cutSpace Gp := by
-- proof
  apply StatMech.Ising.even_to_cut_of_cycleParity hG ψ hsymm hcyc

/--
[walkParity_union_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean)
-/
@[path]
private lemma walkParity_union_disjoint_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq V]
  {Gp : SimpleGraph V}
  {δ₁ δ₂ : Finset (Sym2 V)}
  {x y : V}
  {p : Gp.Walk x y}
-- given
  (hdisj : Disjoint δ₁ δ₂) :
-- imply
  walkParity Gp (δ₁ ∪ δ₂) p = (walkParity Gp δ₁ p).xor (walkParity Gp δ₂ p) := by
-- proof
  apply StatMech.Ising.walkParity_union_disjoint hdisj p

/--
[evenOnCycles_union_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean)
-/
@[path]
private lemma evenOnCycles_union_disjoint_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq V]
  {Gp : SimpleGraph V}
  {δ₁ δ₂ : Finset (Sym2 V)}
-- given
  (hdisj : Disjoint δ₁ δ₂)
  (h0 : EvenOnCycles Gp δ₁)
  (h1 : EvenOnCycles Gp δ₂) :
-- imply
  EvenOnCycles Gp (δ₁ ∪ δ₂) := by
-- proof
  apply StatMech.Ising.evenOnCycles_union_disjoint hdisj h0 h1

/--
[walkParity_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean)
-/
@[path]
private lemma walkParity_empty_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq V]
  {Gp : SimpleGraph V}
  {δ₁ δ₂ : Finset (Sym2 V)}
  {Gp : SimpleGraph V}
  {x y : V}
  {p : Gp.Walk x y} :
-- imply
  walkParity Gp (∅ : Finset (Sym2 V)) p = false := by
-- proof
  apply StatMech.Ising.walkParity_empty Gp p

/--
[evenOnCycles_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean)
-/
@[path]
private lemma evenOnCycles_empty_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq V]
  {Gp : SimpleGraph V}
  {δ₁ δ₂ : Finset (Sym2 V)}
  {Gp : SimpleGraph V} :
-- imply
  EvenOnCycles Gp (∅ : Finset (Sym2 V)) := by
-- proof
  apply StatMech.Ising.evenOnCycles_empty Gp

/--
[evenOnCycles_biUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean)
-/
@[path]
private lemma evenOnCycles_biUnion_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq V]
  {Gp : SimpleGraph V}
  {s : Finset ι}
  {pieces : ι → Finset (Sym2 V)}
-- given
  (hdisj : (s : Set ι).PairwiseDisjoint pieces)
  (hpieces : ∀ i ∈ s, EvenOnCycles Gp (pieces i)) :
-- imply
  EvenOnCycles Gp (s.biUnion pieces) := by
-- proof
  apply StatMech.Ising.evenOnCycles_biUnion s pieces hdisj hpieces

/--
[cycleParityCompatible_of_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean)
-/
@[path]
private lemma cycleParityCompatible_of_decomposition_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype V]
  [DecidableEq V]
  {ψ : Sym2 V ≃ Sym2 V}
  {cycleSets : Finset (Sym2 V) → Prop}
  {F : Finset (Sym2 V)}
  {s : Finset ι}
  {pieces : ι → Finset (Sym2 V)}
-- given
  (hsingle : SingleDualCycleParity Gp ψ cycleSets)
  (hcov : F = s.biUnion pieces)
  (hdisj : (s : Set ι).PairwiseDisjoint pieces)
  (hcyc : ∀ i ∈ s, cycleSets (pieces i)) :
-- imply
  CycleParityCompatible Gp ψ F := by
-- proof
  apply StatMech.Ising.cycleParityCompatible_of_decomposition ψ hsingle s pieces hcov hdisj hcyc

/--
[even_to_cut_of_closedWalkParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean)
-/
@[path]
private lemma even_to_cut_of_closedWalkParity_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {ψ : Sym2 V ≃ Sym2 V}
-- given
  (hG : Gp.Preconnected)
  (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
  (hdecomp : EvenSubgraphWalkDecomp Gd)
  (hlink : ClosedDualWalkParity Gp Gd ψ) :
-- imply
  ∀ F ∈ evenSubgraphs Gd, (F.image ψ.symm) ∈ cutSpace Gp := by
-- proof
  apply StatMech.Ising.even_to_cut_of_closedWalkParity hG ψ hsymm hdecomp hlink

/--
[edges_eq_nil_of_isEmpty_edgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean)
-/
@[path]
private lemma edges_eq_nil_of_isEmpty_edgeSet_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype V]
  [DecidableEq V]
  {w : V}
  {W : Gd.Walk w w}
-- given
  (hGd : Gd.edgeSet = ∅) :
-- imply
  W.edges = [] := by
-- proof
  apply StatMech.Ising.edges_eq_nil_of_isEmpty_edgeSet hGd W

/--
[closedDualWalkParity_of_edgeless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean)
-/
@[path]
private lemma closedDualWalkParity_of_edgeless_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype V]
  [DecidableEq V]
  {ψ : Sym2 V ≃ Sym2 V}
-- given
  (hGd : Gd.edgeSet = ∅) :
-- imply
  ClosedDualWalkParity Gp Gd ψ := by
-- proof
  apply StatMech.Ising.closedDualWalkParity_of_edgeless ψ hGd


-- created on 2026-10-23
