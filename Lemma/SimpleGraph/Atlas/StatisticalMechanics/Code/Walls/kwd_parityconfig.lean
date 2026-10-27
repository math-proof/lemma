import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.kwd_parityconfig.Part4
open Finset SimpleGraph StatMech StatMech.Walls


/--
[walkPar_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_parityconfig.lean)
-/
@[path]
private lemma walkPar_nil_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {δ : Finset (Sym2 V)}
  {x : V} :
-- imply
  walkPar G δ (.nil : G.Walk x x) = false := by
-- proof
  apply StatMech.Walls.walkPar_nil G δ

/--
[walkPar_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_parityconfig.lean)
-/
@[path]
private lemma walkPar_cons_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {δ : Finset (Sym2 V)}
  {u v w : V}
  {p : G.Walk v w}
-- given
  (h : G.Adj u v) :
-- imply
  walkPar G δ (.cons h p) = (decide (s(u, v) ∈ δ)).xor (walkPar G δ p) := by
-- proof
  apply StatMech.Walls.walkPar_cons G δ h p

/--
[walkPar_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_parityconfig.lean)
-/
@[path]
private lemma walkPar_append_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {δ : Finset (Sym2 V)}
  {G δ}
  {x y z : V}
  {p : G.Walk x y}
  {q : G.Walk y z} :
-- imply
  walkPar G δ (p.append q) = (walkPar G δ p).xor (walkPar G δ q) := by
-- proof
  apply StatMech.Walls.walkPar_append G δ p q

/--
[walkPar_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_parityconfig.lean)
-/
@[path]
private lemma walkPar_reverse_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {δ : Finset (Sym2 V)}
  {G δ}
  {x y : V}
  {p : G.Walk x y} :
-- imply
  walkPar G δ p.reverse = walkPar G δ p := by
-- proof
  apply StatMech.Walls.walkPar_reverse G δ p

/--
[walkPar_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_parityconfig.lean)
-/
@[path]
private lemma walkPar_singleton_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {δ : Finset (Sym2 V)}
  {G δ}
  {x y : V}
-- given
  (h : G.Adj x y) :
-- imply
  walkPar G δ (SimpleGraph.Walk.cons h (.nil : G.Walk y y)) = decide (s(x, y) ∈ δ) := by
-- proof
  apply StatMech.Walls.walkPar_singleton G δ h

/--
[walkPar_eq_of_evenOnAllCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_parityconfig.lean)
-/
@[path]
private lemma walkPar_eq_of_evenOnAllCycles_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {δ : Finset (Sym2 V)}
  (G δ)
  {x y : V}
  {p q : G.Walk x y}
-- given
  (hev : EvenOnAllCycles G δ) :
-- imply
  walkPar G δ p = walkPar G δ q := by
-- proof
  apply StatMech.Walls.walkPar_eq_of_evenOnAllCycles hev p q

/--
[mem_disagree_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_parityconfig.lean)
-/
@[path]
private lemma mem_disagree_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G}
  {c : V → Bool}
  {x y : V}
-- given
  (h : G.Adj x y) :
-- imply
  s(x, y) ∈ disagree G c ↔ c x ≠ c y := by
-- proof
  apply StatMech.Walls.mem_disagree_iff c h

/--
[disagree_subset_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_parityconfig.lean)
-/
@[path]
private lemma disagree_subset_edgeFinset_eq
  [Fintype V]
  [DecidableEq V]
  {G}
  {c : V → Bool} :
-- imply
  disagree G c ⊆ G.edgeFinset := by
-- proof
  apply StatMech.Walls.disagree_subset_edgeFinset c

/--
[walkPar_disagree_eq_xor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_parityconfig.lean)
-/
@[path]
private lemma walkPar_disagree_eq_xor_eq
  [Fintype V]
  [DecidableEq V]
  {c : V → Bool}
  {x y : V}
  {p : G.Walk x y} :
-- imply
  walkPar G (disagree G c) p = (c x).xor (c y) := by
-- proof
  apply StatMech.Walls.walkPar_disagree_eq_xor c p

/--
[disagree_evenOnAllCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_parityconfig.lean)
-/
@[path]
private lemma disagree_evenOnAllCycles_eq
  [Fintype V]
  [DecidableEq V]
  {c : V → Bool} :
-- imply
  EvenOnAllCycles G (disagree G c) := by
-- proof
  apply StatMech.Walls.disagree_evenOnAllCycles c

/--
[parityProp_adj_xor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_parityconfig.lean)
-/
@[path]
private lemma parityProp_adj_xor_eq
  [Fintype V]
  [DecidableEq V]
  {G δ}
  {v₀ : V}
  {x y : V}
-- given
  (hev : EvenOnAllCycles G δ)
  (hG : G.Preconnected)
  (h : G.Adj x y) :
-- imply
  (parityProp G δ hG v₀ x).xor (parityProp G δ hG v₀ y) = decide (s(x, y) ∈ δ) := by
-- proof
  apply StatMech.Walls.parityProp_adj_xor hev hG v₀ h

/--
[disagree_parityProp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_parityconfig.lean)
-/
@[path]
private lemma disagree_parityProp_eq
  [Fintype V]
  [DecidableEq V]
  {G δ}
  {v₀ : V}
-- given
  (hev : EvenOnAllCycles G δ)
  (hG : G.Preconnected)
  (hδ : δ ⊆ G.edgeFinset) :
-- imply
  disagree G (parityProp G δ hG v₀) = δ := by
-- proof
  apply StatMech.Walls.disagree_parityProp hev hG v₀ hδ

/--
[exists_disagree_eq_of_evenOnAllCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_parityconfig.lean)
-/
@[path]
private lemma exists_disagree_eq_of_evenOnAllCycles_eq
  [Fintype V]
  [DecidableEq V]
  {G δ}
  [Nonempty V]
-- given
  (hG : G.Preconnected)
  (hδ : δ ⊆ G.edgeFinset)
  (hev : EvenOnAllCycles G δ) :
-- imply
  ∃ c : V → Bool, disagree G c = δ := by
-- proof
  apply StatMech.Walls.exists_disagree_eq_of_evenOnAllCycles hG hδ hev

/--
[evenOnAllCycles_iff_exists_disagree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_parityconfig.lean)
-/
@[path]
private lemma evenOnAllCycles_iff_exists_disagree_eq
  [Fintype V]
  [DecidableEq V]
  {G δ}
  [Nonempty V]
-- given
  (hG : G.Preconnected)
  (hδ : δ ⊆ G.edgeFinset) :
-- imply
  EvenOnAllCycles G δ ↔ ∃ c : V → Bool, disagree G c = δ := by
-- proof
  apply StatMech.Walls.evenOnAllCycles_iff_exists_disagree hG hδ


-- created on 2026-10-23
