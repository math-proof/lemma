import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc7offboxedgeagree
open Set StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech StatMech.Walls


/--
[bc7_offBox_rho_edge_agree_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7offboxedgeagree.lean)
-/
@[path]
private lemma bc7_offBox_rho_edge_agree_iff_eq
  {d : ℕ}
  {N : ℕ}
  {G : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
  {e : Sym2 (Site d)}
-- given
  (hG : e ∉ G)
  (hbox : e ∉ boxEdges d N) :
-- imply
  removeSite 0 (bc6_closeBoxExcept N G ω) e = removeSite 0 ω e := by
-- proof
  apply StatMech.Walls.bc7_offBox_rho_edge_agree_iff hG hbox

/--
[bc7_offBox_rho_edge_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7offboxedgeagree.lean)
-/
@[path]
private lemma bc7_offBox_rho_edge_agree_eq
  {d : ℕ}
  {N : ℕ}
  {G : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
  {u v : Site d}
-- given
  (hopen : IsOpenEdge d (removeSite 0 (bc6_closeBoxExcept N G ω)) u v)
  (hG : s(u, v) ∉ G)
  (hbox : s(u, v) ∉ boxEdges d N) :
-- imply
  IsOpenEdge d (removeSite 0 ω) u v := by
-- proof
  apply StatMech.Walls.bc7_offBox_rho_edge_agree hopen hG hbox

/--
[bc7_offBox_rho_edge_agree'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7offboxedgeagree.lean)
-/
@[path]
private lemma bc7_offBox_rho_edge_agree'_eq
  {d : ℕ}
  {N : ℕ}
  {G : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
  {u v : Site d}
-- given
  (hopen : IsOpenEdge d (removeSite 0 ω) u v)
  (hG : s(u, v) ∉ G)
  (hbox : s(u, v) ∉ boxEdges d N) :
-- imply
  IsOpenEdge d (removeSite 0 (bc6_closeBoxExcept N G ω)) u v := by
-- proof
  apply StatMech.Walls.bc7_offBox_rho_edge_agree' hopen hG hbox

/--
[bc7_offBox_rho_edge_agree_and_originFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7offboxedgeagree.lean)
-/
@[path]
private lemma bc7_offBox_rho_edge_agree_and_originFree_eq
  {d : ℕ}
  {N : ℕ}
  {G : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
  {u v : Site d}
-- given
  (hopen : IsOpenEdge d (removeSite 0 (bc6_closeBoxExcept N G ω)) u v)
  (hG : s(u, v) ∉ G)
  (hbox : s(u, v) ∉ boxEdges d N) :
-- imply
  (0 : Site d) ∉ s(u, v) ∧ IsOpenEdge d (removeSite 0 ω) u v := by
-- proof
  apply StatMech.Walls.bc7_offBox_rho_edge_agree_and_originFree hopen hG hbox


-- created on 2026-10-23
