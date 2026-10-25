import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
open Set SimpleGraph Finset StatMech.Lattice StatMech.RSW.Box StatMech StatMech.Universality


/--
[jex_leftSide_subset_leftReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/JordanExhaustivityClose.lean)
-/
@[path]
private lemma jex_leftSide_subset_leftReach_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {x : Site 2}
-- given
  (hx : x ∈ leftSide 0 n 0 n) :
-- imply
  x ∈ bcd_leftReach ω n := by
-- proof
  apply StatMech.Universality.jex_leftSide_subset_leftReach ω n hx

/--
[jex_rightSide_notin_leftReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/JordanExhaustivityClose.lean)
-/
@[path]
private lemma jex_rightSide_notin_leftReach_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {y : Site 2}
-- given
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hy : y ∈ rightSide 0 n 0 n) :
-- imply
  y ∉ bcd_leftReach ω n := by
-- proof
  apply StatMech.Universality.jex_rightSide_notin_leftReach ω n hnoH hy

/--
[jex_leftReach_separates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/JordanExhaustivityClose.lean)
-/
@[path]
private lemma jex_leftReach_separates_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {x y : Site 2}
-- given
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hx : x ∈ leftSide 0 n 0 n)
  (hy : y ∈ rightSide 0 n 0 n) :
-- imply
  ¬ (latticeMinusBarrier (bcd_leftReach ω n)).Reachable x y := by
-- proof
  apply StatMech.Universality.jex_leftReach_separates ω n hnoH hx hy

/--
[jex_escape_crossCount_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/JordanExhaustivityClose.lean)
-/
@[path]
private lemma jex_escape_crossCount_odd_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hx : x ∈ leftSide 0 n 0 n)
  (hy : y ∈ rightSide 0 n 0 n) :
-- imply
  ¬ Even (crossCount (bcd_leftReach ω n) w) := by
-- proof
  apply StatMech.Universality.jex_escape_crossCount_odd ω n hnoH hx hy w

/--
[jex_barrier_edge_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/JordanExhaustivityClose.lean)
-/
@[path]
private lemma jex_barrier_edge_closed_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {p q : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj p q)
  (hbd : bdEdge (bcd_leftReach ω n) s(p, q))
  (hpbox : p ∈ rect 0 n 0 n)
  (hqbox : q ∈ rect 0 n 0 n) :
-- imply
  ω s(p, q) = false := by
-- proof
  apply StatMech.Universality.jex_barrier_edge_closed ω n hadj hbd hpbox hqbox

/--
[jex_barrier_dual_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/JordanExhaustivityClose.lean)
-/
@[path]
private lemma jex_barrier_dual_open_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {p q : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj p q)
  (hbd : bdEdge (bcd_leftReach ω n) s(p, q))
  (hpbox : p ∈ rect 0 n 0 n)
  (hqbox : q ∈ rect 0 n 0 n) :
-- imply
  dualConfig ω (crossEdge s(p, q)) = true := by
-- proof
  apply StatMech.Universality.jex_barrier_dual_open ω n hadj hbd hpbox hqbox

/--
[jex_leftReach_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/JordanExhaustivityClose.lean)
-/
@[path]
private lemma jex_leftReach_finite_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ} :
-- imply
  (bcd_leftReach ω n).Finite := by
-- proof
  apply StatMech.Universality.jex_leftReach_finite ω n

/--
[jex_lattice_walk_row](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/JordanExhaustivityClose.lean)
-/
@[path]
private lemma jex_lattice_walk_row_eq
  {c : ℤ}
  {m : ℕ} :
-- imply
  (hypercubicLattice 2).Reachable (![0, c]) (![(m : ℤ), c]) := by
-- proof
  apply StatMech.Universality.jex_lattice_walk_row c m

/--
[jex_edgeBoundary_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/JordanExhaustivityClose.lean)
-/
@[path]
private lemma jex_edgeBoundary_nonempty_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {c : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hc0 : 0 ≤ c)
  (hcn : c ≤ n) :
-- imply
  (edgeBoundary 2 (bcd_leftReach ω n)).Nonempty := by
-- proof
  apply StatMech.Universality.jex_edgeBoundary_nonempty ω hn hnoH hc0 hcn

/--
[jex_exists_dualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/JordanExhaustivityClose.lean)
-/
@[path]
private lemma jex_exists_dualCircuit_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {c : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hc0 : 0 ≤ c)
  (hcn : c ≤ n) :
-- imply
  ∃ (u : Site 2) (cyc : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u), cyc.IsCycle := by
-- proof
  apply StatMech.Universality.jex_exists_dualCircuit ω hn hnoH hc0 hcn

/--
[jex_dualCircuit_edge_dual_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/JordanExhaustivityClose.lean)
-/
@[path]
private lemma jex_dualCircuit_edge_dual_open_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {f g : Site 2}
  {p q : Site 2}
-- given
  (hadj : (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g)
  (hpq : sharedPrimalEdge f g = s(p, q))
  (hpadj : (hypercubicLattice 2).Adj p q)
  (hpbox : p ∈ rect 0 n 0 n)
  (hqbox : q ∈ rect 0 n 0 n) :
-- imply
  dualConfig ω (crossEdge s(p, q)) = true := by
-- proof
  apply StatMech.Universality.jex_dualCircuit_edge_dual_open ω n hadj hpq hpadj hpbox hqbox

/--
[jex_native_dualVerticalCrossing_of_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/JordanExhaustivityClose.lean)
-/
@[path]
private lemma jex_native_dualVerticalCrossing_of_barrier_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (h : jex_DualBarrierVCrossing ω n) :
-- imply
  DualVerticalCrossing ω 0 n 0 n := by
-- proof
  apply StatMech.Universality.jex_native_dualVerticalCrossing_of_barrier ω n h

/--
[jex_exhaustivity_of_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/JordanExhaustivityClose.lean)
-/
@[path]
private lemma jex_exhaustivity_of_barrier_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (_hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (h : jex_DualBarrierVCrossing ω n) :
-- imply
  HorizontalCrossing ω 0 n 0 n ∨ DualVerticalCrossing ω 0 n 0 n := by
-- proof
  apply StatMech.Universality.jex_exhaustivity_of_barrier ω n _hnoH h

/--
[jex_barrier_vcrossing_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/JordanExhaustivityClose.lean)
-/
@[path]
private lemma jex_barrier_vcrossing_nonvacuous_eq :
-- imply
  jex_DualBarrierVCrossing bcc_botCfg 2 := by
-- proof
  apply StatMech.Universality.jex_barrier_vcrossing_nonvacuous

/--
[jex_wall_noH](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/JordanExhaustivityClose.lean)
-/
@[path]
private lemma jex_wall_noH_eq :
-- imply
  ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 := by
-- proof
  apply StatMech.Universality.jex_wall_noH

/--
[jex_wall_separates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/JordanExhaustivityClose.lean)
-/
@[path]
private lemma jex_wall_separates_eq
  {x y : Site 2}
-- given
  (hx : x ∈ leftSide 0 2 0 2)
  (hy : y ∈ rightSide 0 2 0 2) :
-- imply
  ¬ (latticeMinusBarrier (bcd_leftReach bcc_wallCfg 2)).Reachable x y := by
-- proof
  apply StatMech.Universality.jex_wall_separates hx hy

/--
[jex_wall_dualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/JordanExhaustivityClose.lean)
-/
@[path]
private lemma jex_wall_dualCircuit_eq :
-- imply
  ∃ (u : Site 2) (cyc : (faceBoundaryGraph (bcd_leftReach bcc_wallCfg 2)).Walk u u), cyc.IsCycle := by
-- proof
  apply StatMech.Universality.jex_wall_dualCircuit


-- created on 2026-10-23
