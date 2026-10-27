import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bri2reconcile.Part3
open Set SimpleGraph Finset StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Walls


/--
[bri2_G_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bri2reconcile.lean)
-/
@[path]
private lemma bri2_G_adj_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
  {j k : Site 2} :
-- imply
  (bri2_G ω L).Adj j k ↔ (bgf2_Gf ω L).Adj (bgf2_centre L j) (bgf2_centre L k) := by
-- proof
  apply StatMech.Walls.bri2_G_adj ω L j k

/--
[bri2_q_centre_imp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bri2reconcile.lean)
-/
@[path]
private lemma bri2_q_centre_imp_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
  {a j : Site 2}
-- given
  (h : bgf2_q ω L a = bgf2_centre L j) :
-- imply
  bgn_idx L a = j := by
-- proof
  apply StatMech.Walls.bri2_q_centre_imp h

/--
[bri2_q_centre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bri2reconcile.lean)
-/
@[path]
private lemma bri2_q_centre_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
  {j : Site 2} :
-- imply
  bgf2_q ω L (bgf2_centre L j) = bgf2_centre L j := by
-- proof
  apply StatMech.Walls.bri2_q_centre ω L j

/--
[bri2_le_bgn_Gn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bri2reconcile.lean)
-/
@[path]
private lemma bri2_le_bgn_Gn_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ} :
-- imply
  bri2_G ω L ≤ bgn_Gn ω L := by
-- proof
  apply StatMech.Walls.bri2_le_bgn_Gn ω L

/--
[bri2_le_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bri2reconcile.lean)
-/
@[path]
private lemma bri2_le_lattice_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ} :
-- imply
  bri2_G ω L ≤ hypercubicLattice 2 := by
-- proof
  apply StatMech.Walls.bri2_le_lattice ω L

/--
[bri2_faithful_sound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bri2reconcile.lean)
-/
@[path]
private lemma bri2_faithful_sound_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
  {j k : Site 2}
-- given
  (h : (bri2_G ω L).Reachable j k) :
-- imply
  Connected 2 ω (bgf2_centre L j) (bgf2_centre L k) := by
-- proof
  apply StatMech.Walls.bri2_faithful_sound h

/--
[bri2_sep_sound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bri2reconcile.lean)
-/
@[path]
private lemma bri2_sep_sound_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
  {j₀ j k : Site 2}
-- given
  (h : ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j₀)).Reachable (bgf2_centre L j) (bgf2_centre L k)) :
-- imply
  ¬ (bkg_deleteVertex (bri2_G ω L) j₀).Reachable j k := by
-- proof
  apply StatMech.Walls.bri2_sep_sound h


-- created on 2026-10-23
