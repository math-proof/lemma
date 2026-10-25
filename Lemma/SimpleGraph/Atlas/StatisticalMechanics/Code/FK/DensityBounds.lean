import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.DensityBounds
open StatMech StatMech.FK


/--
[edgeMarginalOpen_eq_closedFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityBounds.lean)
-/
@[path]
private lemma edgeMarginalOpen_eq_closedFiber_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {e : Sym2 V} :
-- imply
  edgeMarginalOpen G p q e = ∑ ψ ∈ Finset.univ.filter (fun ψ : ConfigSpace (Sym2 V) => ψ e = false), fkProb G p q (setOpen e ψ) := by
-- proof
  apply StatMech.FK.edgeMarginalOpen_eq_closedFiber G p q e

/--
[closedFiber_pairMass_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityBounds.lean)
-/
@[path]
private lemma closedFiber_pairMass_eq_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {e : Sym2 V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ∑ ψ ∈ Finset.univ.filter (fun ψ : ConfigSpace (Sym2 V) => ψ e = false), (fkProb G p q (setOpen e ψ) + fkProb G p q (setClosed e ψ)) = 1 := by
-- proof
  apply StatMech.FK.closedFiber_pairMass_eq_one G hp hp1 hq e

/--
[condOpen_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityBounds.lean)
-/
@[path]
private lemma condOpen_setOpen_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {e : Sym2 V}
  {ψ : ConfigSpace (Sym2 V)} :
-- imply
  condOpen G p q e (setOpen e ψ) = condOpen G p q e ψ := by
-- proof
  apply StatMech.FK.condOpen_setOpen G p q e ψ

/--
[fkProb_setOpen_eq_condOpen_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityBounds.lean)
-/
@[path]
private lemma fkProb_setOpen_eq_condOpen_mul_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {e : Sym2 V}
  {ψ : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  fkProb G p q (setOpen e ψ) = condOpen G p q e ψ * (fkProb G p q (setOpen e ψ) + fkProb G p q (setClosed e ψ)) := by
-- proof
  apply StatMech.FK.fkProb_setOpen_eq_condOpen_mul G hp hp1 hq e ψ

/--
[condInterval_sandwiches_marginal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityBounds.lean)
-/
@[path]
private lemma condInterval_sandwiches_marginal_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {e : Sym2 V}
  {lo hi : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hlo : ∀ ψ : ConfigSpace (Sym2 V), lo ≤ condOpen G p q e ψ)
  (hhi : ∀ ψ : ConfigSpace (Sym2 V), condOpen G p q e ψ ≤ hi) :
-- imply
  lo ≤ edgeMarginalOpen G p q e ∧ edgeMarginalOpen G p q e ≤ hi := by
-- proof
  apply StatMech.FK.condInterval_sandwiches_marginal G hp hp1 hq e hlo hhi

/--
[edge_density_finiteEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityBounds.lean)
-/
@[path]
private lemma edge_density_finiteEnergy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {e : Sym2 V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  cFE p q ≤ edgeMarginalOpen G p q e ∧ edgeMarginalOpen G p q e ≤ 1 - cFE p q := by
-- proof
  apply StatMech.FK.edge_density_finiteEnergy G hp hp1 hq e

/--
[edge_density_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityBounds.lean)
-/
@[path]
private lemma edge_density_bounds_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {e : Sym2 V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (he : e ∈ G.edgeFinset) :
-- imply
  p / (p + q * (1 - p)) ≤ edgeMarginalOpen G p q e ∧ edgeMarginalOpen G p q e ≤ p := by
-- proof
  apply StatMech.FK.edge_density_bounds G hp hp1 hq he


-- created on 2026-10-23
