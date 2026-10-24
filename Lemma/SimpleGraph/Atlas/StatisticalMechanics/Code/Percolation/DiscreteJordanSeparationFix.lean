import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.DiscreteJordanSeparationFix
open Set SimpleGraph Function StatMech StatMech.Percolation


/--
[djfx_separation'_holds_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DiscreteJordanSeparationFix.lean)
-/
@[path]
private lemma djfx_separation'_holds_empty_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a b : Site 2}
-- given
  (hpos : ∃ a' : Site 2, (faceBoundaryGraph (∅ : Set (Site 2))).Adj a a')
  (_hreach : (faceBoundaryGraph (∅ : Set (Site 2))).Reachable a b) :
-- imply
  ∃ c : (faceBoundaryGraph (∅ : Set (Site 2))).Walk a a, c.IsCycle ∧ b ∈ c.support := by
-- proof
  apply StatMech.Percolation.djfx_separation'_holds_empty hpos _hreach

/--
[djfx_faceBoundaryGraph_edgeCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DiscreteJordanSeparationFix.lean)
-/
@[path]
private lemma djfx_faceBoundaryGraph_edgeCycle_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {v w : Site 2}
-- given
  (hK : K.Finite)
  (hadj : (faceBoundaryGraph K).Adj v w) :
-- imply
  ∃ c : (faceBoundaryGraph K).Walk v v, c.IsCycle ∧ w ∈ c.support := by
-- proof
  apply StatMech.Percolation.djfx_faceBoundaryGraph_edgeCycle K hK hadj

/--
[djfx_edgeCycle_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DiscreteJordanSeparationFix.lean)
-/
@[path]
private lemma djfx_edgeCycle_self_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {v w : Site 2}
-- given
  (hK : K.Finite)
  (hadj : (faceBoundaryGraph K).Adj v w) :
-- imply
  ∃ c : (faceBoundaryGraph K).Walk v v, c.IsCycle ∧ v ∈ c.support := by
-- proof
  apply StatMech.Percolation.djfx_edgeCycle_self K hK hadj

/--
[djfx_exitFaceUp_edge_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DiscreteJordanSeparationFix.lean)
-/
@[path]
private lemma djfx_exitFaceUp_edge_endpoint_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  ∃ a' : Site 2, (faceBoundaryGraph (cluster 2 ω (origin 2))).Adj (exitFaceUp (ω := ω) hfin) a' := by
-- proof
  apply StatMech.Percolation.djfx_exitFaceUp_edge_endpoint hfin

/--
[djfx_enclosingContourLinksExits_of_sep'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DiscreteJordanSeparationFix.lean)
-/
@[path]
private lemma djfx_enclosingContourLinksExits_of_sep'_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hsep : djfx_DiscreteJordanSeparation')
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hsame : ExitDartsSameOrbit ω hfin) :
-- imply
  EnclosingContourLinksExits ω hfin := by
-- proof
  apply StatMech.Percolation.djfx_enclosingContourLinksExits_of_sep' hsep hfin hsame

/--
[djfx_pcAnchoredEnclosure_of_sep'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DiscreteJordanSeparationFix.lean)
-/
@[path]
private lemma djfx_pcAnchoredEnclosure_of_sep'_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hsep : djfx_DiscreteJordanSeparation')
  (hsame : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), ExitDartsSameOrbit ω hfin) :
-- imply
  PcAnchoredEnclosure := by
-- proof
  apply StatMech.Percolation.djfx_pcAnchoredEnclosure_of_sep' hsep hsame

/--
[djfx_pc_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DiscreteJordanSeparationFix.lean)
-/
@[path]
private lemma djfx_pc_lt_one_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hsep : djfx_DiscreteJordanSeparation')
  (hsame : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), ExitDartsSameOrbit ω hfin) :
-- imply
  pc 2 < 1 := by
-- proof
  apply StatMech.Percolation.djfx_pc_lt_one hsep hsame

/--
[djfx_pc_pos_and_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DiscreteJordanSeparationFix.lean)
-/
@[path]
private lemma djfx_pc_pos_and_lt_one_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hsep : djfx_DiscreteJordanSeparation')
  (hsame : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), ExitDartsSameOrbit ω hfin) :
-- imply
  0 < pc 2 ∧ pc 2 < 1 := by
-- proof
  apply StatMech.Percolation.djfx_pc_pos_and_lt_one hsep hsame


-- created on 2026-10-23
