import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc6edgedichotomy
open Set StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech StatMech.Walls


/--
[bc6_closeBoxExcept_of_mem_G](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6edgedichotomy.lean)
-/
@[path]
private lemma bc6_closeBoxExcept_of_mem_G_eq
  {d : ℕ}
  {N : ℕ}
  {G : Finset (Sym2 (Site d))}
  {e : Sym2 (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : e ∈ G) :
-- imply
  bc6_closeBoxExcept N G ω e = true := by
-- proof
  apply StatMech.Walls.bc6_closeBoxExcept_of_mem_G h ω

/--
[bc6_closeBoxExcept_of_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6edgedichotomy.lean)
-/
@[path]
private lemma bc6_closeBoxExcept_of_mem_box_eq
  {d : ℕ}
  {N : ℕ}
  {G : Finset (Sym2 (Site d))}
  {e : Sym2 (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hG : e ∉ G)
  (hbox : e ∈ boxEdges d N) :
-- imply
  bc6_closeBoxExcept N G ω e = false := by
-- proof
  apply StatMech.Walls.bc6_closeBoxExcept_of_mem_box hG hbox ω

/--
[bc6_closeBoxExcept_of_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6edgedichotomy.lean)
-/
@[path]
private lemma bc6_closeBoxExcept_of_outside_eq
  {d : ℕ}
  {N : ℕ}
  {G : Finset (Sym2 (Site d))}
  {e : Sym2 (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hG : e ∉ G)
  (hbox : e ∉ boxEdges d N) :
-- imply
  bc6_closeBoxExcept N G ω e = ω e := by
-- proof
  apply StatMech.Walls.bc6_closeBoxExcept_of_outside hG hbox ω

/--
[bc6_closeBoxExcept_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6edgedichotomy.lean)
-/
@[path]
private lemma bc6_closeBoxExcept_le_eq
  {d : ℕ}
  {N : ℕ}
  {G : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
  {e : Sym2 (Site d)}
-- given
  (h : bc6_closeBoxExcept N G ω e = true)
  (hG : e ∉ G) :
-- imply
  e ∉ boxEdges d N ∧ ω e = true := by
-- proof
  apply StatMech.Walls.bc6_closeBoxExcept_le G ω h hG

/--
[bc6_closeBoxExceptEdge_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6edgedichotomy.lean)
-/
@[path]
private lemma bc6_closeBoxExceptEdge_cases_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {N : ℕ}
  {G : Finset (Sym2 (Site d))}
  {e : Sym2 (Site d)}
-- given
  (h : removeSite 0 (bc6_closeBoxExcept N G ω) e = true) :
-- imply
  (0 : Site d) ∉ e ∧ (e ∈ G ∨ (ω e = true ∧ e ∉ boxEdges d N)) := by
-- proof
  apply StatMech.Walls.bc6_closeBoxExceptEdge_cases ω N G h

/--
[bc6_origin_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6edgedichotomy.lean)
-/
@[path]
private lemma bc6_origin_notMem_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {N : ℕ}
  {G : Finset (Sym2 (Site d))}
  {e : Sym2 (Site d)}
-- given
  (h : removeSite 0 (bc6_closeBoxExcept N G ω) e = true) :
-- imply
  (0 : Site d) ∉ e := by
-- proof
  apply StatMech.Walls.bc6_origin_notMem ω N G h

/--
[bc6_endpoints_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6edgedichotomy.lean)
-/
@[path]
private lemma bc6_endpoints_ne_zero_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {N : ℕ}
  {G : Finset (Sym2 (Site d))}
  {x y : Site d}
-- given
  (h : removeSite 0 (bc6_closeBoxExcept N G ω) s(x, y) = true) :
-- imply
  x ≠ (0 : Site d) ∧ y ≠ (0 : Site d) := by
-- proof
  apply StatMech.Walls.bc6_endpoints_ne_zero ω N G h

/--
[bc6_corridor_or_outsideBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6edgedichotomy.lean)
-/
@[path]
private lemma bc6_corridor_or_outsideBox_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {N : ℕ}
  {G : Finset (Sym2 (Site d))}
  {e : Sym2 (Site d)}
-- given
  (h : removeSite 0 (bc6_closeBoxExcept N G ω) e = true) :
-- imply
  e ∈ G ∨ (ω e = true ∧ e ∉ boxEdges d N) := by
-- proof
  apply StatMech.Walls.bc6_corridor_or_outsideBox ω N G h

/--
[bc6_endpoint_outside_box_of_not_boxEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6edgedichotomy.lean)
-/
@[path]
private lemma bc6_endpoint_outside_box_of_not_boxEdge_eq
  {d : ℕ}
  {N : ℕ}
  {x y : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj x y)
  (hnb : s(x, y) ∉ boxEdges d N) :
-- imply
  x ∉ box d N ∨ y ∉ box d N := by
-- proof
  apply StatMech.Walls.bc6_endpoint_outside_box_of_not_boxEdge hadj hnb

/--
[bc6_isOpenEdge_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6edgedichotomy.lean)
-/
@[path]
private lemma bc6_isOpenEdge_dichotomy_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {N : ℕ}
  {G : Finset (Sym2 (Site d))}
  {x y : Site d}
-- given
  (h : IsOpenEdge d (removeSite 0 (bc6_closeBoxExcept N G ω)) x y) :
-- imply
  (hypercubicLattice d).Adj x y ∧ (0 : Site d) ∉ s(x, y) ∧ (s(x, y) ∈ G ∨ (ω s(x, y) = true ∧ s(x, y) ∉ boxEdges d N)) := by
-- proof
  apply StatMech.Walls.bc6_isOpenEdge_dichotomy ω N G h

/--
[bc6_edgeDichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6edgedichotomy.lean)
-/
@[path]
private lemma bc6_edgeDichotomy_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {N : ℕ}
  {G : Finset (Sym2 (Site d))}
  {u v : Site d}
-- given
  (h : IsOpenEdge d (removeSite 0 (bc6_closeBoxExcept N G ω)) u v) :
-- imply
  (hypercubicLattice d).Adj u v ∧ (0 : Site d) ∉ s(u, v) ∧ (s(u, v) ∈ G ∨ (ω s(u, v) = true ∧ (u ∉ box d N ∨ v ∉ box d N))) := by
-- proof
  apply StatMech.Walls.bc6_edgeDichotomy ω N G h

/--
[bc6_openSubgraph_le_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6edgedichotomy.lean)
-/
@[path]
private lemma bc6_openSubgraph_le_lattice_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {N : ℕ}
  {G : Finset (Sym2 (Site d))} :
-- imply
  openSubgraph d (removeSite 0 (bc6_closeBoxExcept N G ω)) ≤ hypercubicLattice d := by
-- proof
  apply StatMech.Walls.bc6_openSubgraph_le_lattice ω N G

/--
[bc6_edgeSet_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6edgedichotomy.lean)
-/
@[path]
private lemma bc6_edgeSet_cases_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {N : ℕ}
  {G : Finset (Sym2 (Site d))}
  {e : Sym2 (Site d)}
-- given
  (h : e ∈ (openSubgraph d (removeSite 0 (bc6_closeBoxExcept N G ω))).edgeSet) :
-- imply
  e ∈ (hypercubicLattice d).edgeSet ∧ (0 : Site d) ∉ e ∧ (e ∈ G ∨ (ω e = true ∧ e ∉ boxEdges d N)) := by
-- proof
  apply StatMech.Walls.bc6_edgeSet_cases ω N G h

/--
[bc6_isOpenEdge_dichotomy_corridor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6edgedichotomy.lean)
-/
@[path]
private lemma bc6_isOpenEdge_dichotomy_corridor_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {N : ℕ}
  {j₁ j₂ j₃ : Fin d}
  {L₁ L₂ L₃ : ℕ}
  {x y : Site d}
-- given
  (h : IsOpenEdge d (removeSite 0 (bc6_closeBoxExcept N (hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₂ (L₂ + 1) ∪ hrHD_corridorEdges j₃ (L₃ + 1)) ω)) x y) :
-- imply
  (hypercubicLattice d).Adj x y ∧ (0 : Site d) ∉ s(x, y) ∧ (s(x, y) ∈ hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₂ (L₂ + 1) ∪ hrHD_corridorEdges j₃ (L₃ + 1) ∨ (ω s(x, y) = true ∧ s(x, y) ∉ boxEdges d N)) := by
-- proof
  apply StatMech.Walls.bc6_isOpenEdge_dichotomy_corridor ω N j₁ j₂ j₃ L₁ L₂ L₃ h

/--
[bc6_edgedichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6edgedichotomy.lean)
-/
@[path]
private lemma bc6_edgedichotomy_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {N : ℕ}
  {G : Finset (Sym2 (Site d))}
  {x y : Site d}
-- given
  (h : IsOpenEdge d (removeSite 0 (bc6_closeBoxExcept N G ω)) x y) :
-- imply
  (hypercubicLattice d).Adj x y ∧ (0 : Site d) ∉ s(x, y) ∧ (s(x, y) ∈ G ∨ (ω s(x, y) = true ∧ s(x, y) ∉ boxEdges d N)) := by
-- proof
  apply StatMech.Walls.bc6_edgedichotomy ω N G h


-- created on 2026-10-23
