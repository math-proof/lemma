import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.atcattachstep
open Finset Set SimpleGraph StatMech StatMech.Walls


/--
[atc_exists_extremeCell_finset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atcattachstep.lean)
-/
@[path]
private lemma atc_exists_extremeCell_finset_eq
  {K : Finset (Site 2)}
-- given
  (hne : K.Nonempty) :
-- imply
  ∃ c ∈ K, IsExtremeCell (↑K : Set (Site 2)) c := by
-- proof
  apply StatMech.Walls.atc_exists_extremeCell_finset K hne

/--
[atc_induce_insert_reachable_from_anchor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atcattachstep.lean)
-/
@[path]
private lemma atc_induce_insert_reachable_from_anchor_eq
  {G : SimpleGraph V}
  {S : Set V}
  {w : V}
  {s₀ n : V}
-- given
  (hwS : w ∉ S)
  (hs₀ : s₀ ∈ S)
  (hn : n ∈ S)
  (hadj : G.Adj w n)
  (hreach : ∀ v : S, (G.induce S).Reachable ⟨s₀, hs₀⟩ v) :
-- imply
  ∀ v : (insert w S : Set V), (G.induce (insert w S : Set V)).Reachable ⟨s₀, Set.mem_insert_of_mem w hs₀⟩ v := by
-- proof
  apply StatMech.Walls.atc_induce_insert_reachable_from_anchor G S w hwS hs₀ hn hadj hreach

/--
[atc_compl_erase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atcattachstep.lean)
-/
@[path]
private lemma atc_compl_erase_eq
  {K : Finset (Site 2)}
  {c : Site 2}
-- given
  (hc : c ∈ K) :
-- imply
  ((↑(K.erase c) : Set (Site 2))ᶜ) = insert c ((↑K : Set (Site 2))ᶜ) := by
-- proof
  apply StatMech.Walls.atc_compl_erase hc

/--
[atc_holeFree_erase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atcattachstep.lean)
-/
@[path]
private lemma atc_holeFree_erase_eq
  {K : Finset (Site 2)}
  {c : Site 2}
  {n : Site 2}
-- given
  (hc : c ∈ K)
  (hhf : pc2_HoleFree (↑K : Set (Site 2)))
  (hn : n ∉ K)
  (hadj : (hypercubicLattice 2).Adj c n) :
-- imply
  pc2_HoleFree (↑(K.erase c) : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.atc_holeFree_erase hc hhf hn hadj

/--
[atc_latAdj_top'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atcattachstep.lean)
-/
@[path]
private lemma atc_latAdj_top'_eq
  {c : Site 2} :
-- imply
  (hypercubicLattice 2).Adj c ![c 0, c 1 + 1] := by
-- proof
  apply StatMech.Walls.atc_latAdj_top' c

/--
[atc_extremeCell_top_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atcattachstep.lean)
-/
@[path]
private lemma atc_extremeCell_top_nmem_eq
  {K : Finset (Site 2)}
  {c : Site 2}
-- given
  (hc : IsExtremeCell (↑K : Set (Site 2)) c) :
-- imply
  (![c 0, c 1 + 1] : Site 2) ∉ K := by
-- proof
  apply StatMech.Walls.atc_extremeCell_top_nmem hc

/--
[atc_holeFree_erase_extremeCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atcattachstep.lean)
-/
@[path]
private lemma atc_holeFree_erase_extremeCell_eq
  {K : Finset (Site 2)}
  {c : Site 2}
-- given
  (hcK : c ∈ K)
  (hc : IsExtremeCell (↑K : Set (Site 2)) c)
  (hhf : pc2_HoleFree (↑K : Set (Site 2))) :
-- imply
  pc2_HoleFree (↑(K.erase c) : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.atc_holeFree_erase_extremeCell hcK hc hhf

/--
[atc_hasRemovableCell_of_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atcattachstep.lean)
-/
@[path]
private lemma atc_hasRemovableCell_of_conn_eq
-- given
  (h : atc_HasRemovableConnCell) :
-- imply
  fbc_HasRemovableCell := by
-- proof
  apply StatMech.Walls.atc_hasRemovableCell_of_conn h


-- created on 2026-10-23
