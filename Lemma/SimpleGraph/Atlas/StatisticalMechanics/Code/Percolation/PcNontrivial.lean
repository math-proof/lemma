import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.PcNontrivial
open MeasureTheory Set SimpleGraph Finset StatMech StatMech.Percolation


/--
[cylinder_all_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcNontrivial.lean)
-/
@[path]
private lemma cylinder_all_open_eq
  {d : ℕ}
  {F : Finset (Sym2 (Site d))}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp) ((F : Set (Sym2 (Site d))).pi (fun _ => ({true} : Set Bool))) = (p : ℝ≥0∞) ^ F.card := by
-- proof
  apply StatMech.Percolation.cylinder_all_open p hp F

/--
[adj_coordShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcNontrivial.lean)
-/
@[path]
private lemma adj_coordShift_eq
  {d : ℕ}
  {x : Site d}
  {i : Fin d}
  {b : Bool} :
-- imply
  (hypercubicLattice d).Adj x (coordShift x i (stepSign b)) := by
-- proof
  apply StatMech.Percolation.adj_coordShift x i b

/--
[adj_exists_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcNontrivial.lean)
-/
@[path]
private lemma adj_exists_dir_eq
  {d : ℕ}
  {x y : Site d}
-- given
  (h : (hypercubicLattice d).Adj x y) :
-- imply
  ∃ (i : Fin d) (b : Bool), y = coordShift x i (stepSign b) := by
-- proof
  apply StatMech.Percolation.adj_exists_dir h

/--
[l1_getVert_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcNontrivial.lean)
-/
@[path]
private lemma l1_getVert_le_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {v : Site d}
  {q : (openSubgraph d ω).Walk (origin d) v}
  {k : ℕ} :
-- imply
  (∑ i, (q.getVert k i).natAbs) ≤ k := by
-- proof
  apply StatMech.Percolation.l1_getVert_le q k

/--
[vertOf_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcNontrivial.lean)
-/
@[path]
private lemma vertOf_succ_eq
  {d : ℕ}
  {g : ℕ → Fin d × Bool}
  {k : ℕ} :
-- imply
  vertOf g (k + 1) = coordShift (vertOf g k) (g k).1 (stepSign (g k).2) := by
-- proof
  apply StatMech.Percolation.vertOf_succ g k

/--
[edgeOf_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcNontrivial.lean)
-/
@[path]
private lemma edgeOf_injOn_eq
  {d : ℕ}
  {g : ℕ → Fin d × Bool}
  {n : ℕ}
-- given
  (hg : goodWord g n) :
-- imply
  Set.InjOn (edgeOf g) (Finset.range n) := by
-- proof
  apply StatMech.Percolation.edgeOf_injOn g n hg

/--
[wordEvent_eq_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcNontrivial.lean)
-/
@[path]
private lemma wordEvent_eq_pi_eq
  {d : ℕ}
  {g : ℕ → Fin d × Bool}
  {n : ℕ} :
-- imply
  wordEvent g n = (((Finset.range n).image (edgeOf g) : Finset (Sym2 (Site d))) : Set (Sym2 (Site d))).pi (fun _ => ({true} : Set Bool)) := by
-- proof
  apply StatMech.Percolation.wordEvent_eq_pi g n

/--
[wordEvent_prob_good](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcNontrivial.lean)
-/
@[path]
private lemma wordEvent_prob_good_eq
  {d : ℕ}
  {g : ℕ → Fin d × Bool}
  {n : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hg : goodWord g n) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp) (wordEvent g n) = (p : ℝ≥0∞) ^ n := by
-- proof
  apply StatMech.Percolation.wordEvent_prob_good p hp g n hg

/--
[dirOf_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcNontrivial.lean)
-/
@[path]
private lemma dirOf_spec_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {v : Site d}
  {q : (openSubgraph d ω).Walk (origin d) v}
  {k : ℕ}
-- given
  (hd : 0 < d)
  (hk : k < q.length) :
-- imply
  q.getVert (k + 1) = coordShift (q.getVert k) (dirOf hd q k).1 (stepSign (dirOf hd q k).2) := by
-- proof
  apply StatMech.Percolation.dirOf_spec hd q k hk

/--
[vertOf_dirOf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcNontrivial.lean)
-/
@[path]
private lemma vertOf_dirOf_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {v : Site d}
  {q : (openSubgraph d ω).Walk (origin d) v}
  {j : ℕ}
-- given
  (hd : 0 < d)
  (hj : j ≤ q.length) :
-- imply
  vertOf (dirOf hd q) j = q.getVert j := by
-- proof
  apply StatMech.Percolation.vertOf_dirOf hd q j hj

/--
[percolationEvent_subset_iUnion_wordEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcNontrivial.lean)
-/
@[path]
private lemma percolationEvent_subset_iUnion_wordEvent_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hd : 0 < d) :
-- imply
  percolationEvent d ⊆ ⋃ (g : ℕ → Fin d × Bool) (_ : goodWord g n), wordEvent g n := by
-- proof
  apply StatMech.Percolation.percolationEvent_subset_iUnion_wordEvent hd n

/--
[measure_percolationEvent_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcNontrivial.lean)
-/
@[path]
private lemma measure_percolationEvent_le_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hd : 0 < d)
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp) (percolationEvent d) ≤ ((2 * d : ℝ≥0) * p) ^ n := by
-- proof
  apply StatMech.Percolation.measure_percolationEvent_le hd p hp n

/--
[theta_le_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcNontrivial.lean)
-/
@[path]
private lemma theta_le_pow_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hd : 0 < d)
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  theta d p hp ≤ ((2 * d : ℝ≥0) * p) ^ n := by
-- proof
  apply StatMech.Percolation.theta_le_pow hd p hp n

/--
[theta_eq_zero_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcNontrivial.lean)
-/
@[path]
private lemma theta_eq_zero_of_lt_eq
  {d : ℕ}
-- given
  (hd : 0 < d)
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hsmall : ((2 * d : ℝ≥0) * p : ℝ) < 1) :
-- imply
  theta d p hp = 0 := by
-- proof
  apply StatMech.Percolation.theta_eq_zero_of_lt hd p hp hsmall

/--
[mem_subcriticalSet_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcNontrivial.lean)
-/
@[path]
private lemma mem_subcriticalSet_of_lt_eq
  {d : ℕ}
-- given
  (hd : 0 < d)
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hsmall : ((2 * d : ℝ≥0) * p : ℝ) < 1) :
-- imply
  p ∈ subcriticalSet d := by
-- proof
  apply StatMech.Percolation.mem_subcriticalSet_of_lt hd p hp hsmall

/--
[subcriticalSet_bddAbove](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcNontrivial.lean)
-/
@[path]
private lemma subcriticalSet_bddAbove_eq
  {d : ℕ} :
-- imply
  BddAbove (subcriticalSet d) := by
-- proof
  apply StatMech.Percolation.subcriticalSet_bddAbove

/--
[le_pc_of_mem_subcriticalSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcNontrivial.lean)
-/
@[path]
private lemma le_pc_of_mem_subcriticalSet_eq
  {d : ℕ}
  {p : ℝ≥0}
-- given
  (hp : p ∈ subcriticalSet d) :
-- imply
  p ≤ pc d := by
-- proof
  apply StatMech.Percolation.le_pc_of_mem_subcriticalSet hp

/--
[pc_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcNontrivial.lean)
-/
@[path]
private lemma pc_pos_eq
  {d : ℕ}
-- given
  (hd : 0 < d) :
-- imply
  0 < pc d := by
-- proof
  apply StatMech.Percolation.pc_pos hd

/--
[pc_pos_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcNontrivial.lean)
-/
@[path]
private lemma pc_pos_of_two_le_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d) :
-- imply
  0 < pc d := by
-- proof
  apply StatMech.Percolation.pc_pos_of_two_le hd


-- created on 2026-10-23
