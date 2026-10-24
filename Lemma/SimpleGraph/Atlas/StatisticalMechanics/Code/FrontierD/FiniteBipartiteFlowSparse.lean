import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FiniteBipartiteFlowSparse
open Finset StatMech StatMech.FrontierD


/--
[bipartiteEdgeIncidence_connected_of_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteBipartiteFlowSparse.lean)
-/
@[path]
private lemma bipartiteEdgeIncidence_connected_of_root_eq
  {left : E → P}
  {right : E → D}
  {root : E}
-- given
  (hroot : ∀ e, (bipartiteEdgeIncidenceGraph left right).Reachable root e) :
-- imply
  (bipartiteEdgeIncidenceGraph left right).Connected := by
-- proof
  apply StatMech.FrontierD.bipartiteEdgeIncidence_connected_of_root left right root hroot

/--
[bipartiteEdgeIncidence_cutExpansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteBipartiteFlowSparse.lean)
-/
@[path]
private lemma bipartiteEdgeIncidence_cutExpansion_eq
  [Fintype E]
  [DecidableEq P]
  [DecidableEq D]
  {left : E → P}
  {right : E → D}
-- given
  (hconn : (bipartiteEdgeIncidenceGraph left right).Connected) :
-- imply
  ∀ T : Finset E, T.Nonempty → T ≠ Finset.univ → ∃ e ∉ T, left e ∈ T.image left ∨ right e ∈ T.image right := by
-- proof
  apply StatMech.FrontierD.bipartiteEdgeIncidence_cutExpansion left right hconn

/--
[bipartiteSubsetSparse_of_cutExpansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteBipartiteFlowSparse.lean)
-/
@[path]
private lemma bipartiteSubsetSparse_of_cutExpansion_eq
  [Fintype E]
  [DecidableEq P]
  [DecidableEq D]
  {left : E → P}
  {right : E → D}
-- given
  (hfull : Fintype.card E ≤ (Finset.univ.image left).card + (Finset.univ.image right).card)
  (hcut : ∀ T : Finset E, T.Nonempty → T ≠ Finset.univ → ∃ e ∉ T, left e ∈ T.image left ∨ right e ∈ T.image right) :
-- imply
  ∀ T : Finset E, T.card ≤ (T.image left).card + (T.image right).card := by
-- proof
  apply StatMech.FrontierD.bipartiteSubsetSparse_of_cutExpansion left right hfull hcut

/--
[sparseBipartiteFlow_leftFiber_card_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteBipartiteFlowSparse.lean)
-/
@[path]
private lemma sparseBipartiteFlow_leftFiber_card_le_two_eq
  [Fintype E]
  [DecidableEq P]
  [DecidableEq D]
  [DecidableEq A]
  [AddCommMonoid A]
  {left : E → P}
  {right : E → D}
  {weight : E → A}
  {p : P}
-- given
  (hsparse : ∀ T : Finset E, T.card ≤ (T.image left).card + (T.image right).card)
  (hleft : ∀ p : P, (∑ e ∈ (Finset.univ.filter fun e ↦ weight e ≠ 0).filter (fun e ↦ left e = p), weight e) = 0)
  (hright : ∀ d : D, (∑ e ∈ (Finset.univ.filter fun e ↦ weight e ≠ 0).filter (fun e ↦ right e = d), weight e) = 0) :
-- imply
  (Finset.univ.filter fun e ↦ left e = p ∧ weight e ≠ 0).card ≤ 2 := by
-- proof
  apply StatMech.FrontierD.sparseBipartiteFlow_leftFiber_card_le_two left right weight hsparse hleft hright p

/--
[connectedBipartiteFlow_leftFiber_card_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteBipartiteFlowSparse.lean)
-/
@[path]
private lemma connectedBipartiteFlow_leftFiber_card_le_two_eq
  [Fintype E]
  [DecidableEq P]
  [DecidableEq D]
  [DecidableEq A]
  [AddCommMonoid A]
  {left : E → P}
  {right : E → D}
  {weight : E → A}
  {p : P}
-- given
  (hconn : (bipartiteEdgeIncidenceGraph left right).Connected)
  (hfull : Fintype.card E ≤ (Finset.univ.image left).card + (Finset.univ.image right).card)
  (hleft : ∀ p : P, (∑ e ∈ (Finset.univ.filter fun e ↦ weight e ≠ 0).filter (fun e ↦ left e = p), weight e) = 0)
  (hright : ∀ d : D, (∑ e ∈ (Finset.univ.filter fun e ↦ weight e ≠ 0).filter (fun e ↦ right e = d), weight e) = 0) :
-- imply
  (Finset.univ.filter fun e ↦ left e = p ∧ weight e ≠ 0).card ≤ 2 := by
-- proof
  apply StatMech.FrontierD.connectedBipartiteFlow_leftFiber_card_le_two left right weight hconn hfull hleft hright p


-- created on 2026-10-23
