import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.fkc_rqbdd.Part2
open SimpleGraph Filter Topology Set StatMech StatMech.Walls


/--
[fkc_fkWeight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqbdd.lean)
-/
@[path]
private lemma fkc_fkWeight_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq1 : 1 ≤ q) :
-- imply
  fkWeight G p q ω ≤ q ^ Fintype.card V := by
-- proof
  apply StatMech.Walls.fkc_fkWeight_le G hp hp1 hq1 ω

/--
[fkc_fkZEdge_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqbdd.lean)
-/
@[path]
private lemma fkc_fkZEdge_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq1 : 1 ≤ q) :
-- imply
  ecz_fkZEdge G p q ≤ (2 : ℝ) ^ G.edgeFinset.card * q ^ Fintype.card V := by
-- proof
  apply StatMech.Walls.fkc_fkZEdge_le G hp hp1 hq1

/--
[fkc_edgeFreeEnergy_eq_ecz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqbdd.lean)
-/
@[path]
private lemma fkc_edgeFreeEnergy_eq_ecz_eq
  {d : ℕ}
  {s : ℝ}
  {n : ℕ} :
-- imply
  fkc_edgeFreeEnergy d s 2 n = ecz_edgeFreeEnergy d s n := by
-- proof
  apply StatMech.Walls.fkc_edgeFreeEnergy_eq_ecz d s n

/--
[fkc_rq_bdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqbdd.lean)
-/
@[path]
private lemma fkc_rq_bdd_eq
  {d n : ℕ}
  {s q : ℝ}
-- given
  (hd : 1 ≤ d)
  (hn : 1 ≤ n)
  (hq1 : 1 ≤ q) :
-- imply
  fkc_edgeFreeEnergy d s q n ≤ (Real.log 2 + 2 * Real.log q) + Real.log (1 + Real.exp s) := by
-- proof
  apply StatMech.Walls.fkc_rq_bdd d n hd hn s q hq1


-- created on 2026-10-23
