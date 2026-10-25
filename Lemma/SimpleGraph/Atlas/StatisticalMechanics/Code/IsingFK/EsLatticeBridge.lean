import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.IsingFK.EsLatticeBridge
open StatMech StatMech.IsingFK


/--
[numClustersWired_eq_numClustersBC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsLatticeBridge.lean)
-/
@[path]
private lemma numClustersWired_eq_numClustersBC_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {ω : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop) :
-- imply
  numClustersWired G bdry ω = numClustersBC G (boundaryCliqueGraph bdry) ω := by
-- proof
  apply StatMech.IsingFK.numClustersWired_eq_numClustersBC G bdry ω

/--
[wiredFkWeight_eq_bcWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsLatticeBridge.lean)
-/
@[path]
private lemma wiredFkWeight_eq_bcWeight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop) :
-- imply
  wiredFkWeight G bdry p q ω = bcWeight G (boundaryCliqueGraph bdry) p q ω := by
-- proof
  apply StatMech.IsingFK.wiredFkWeight_eq_bcWeight G bdry p q ω

/--
[wiredFkZ_eq_bcZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsLatticeBridge.lean)
-/
@[path]
private lemma wiredFkZ_eq_bcZ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {p q : ℝ}
-- given
  (bdry : V → Prop) :
-- imply
  wiredFkZ G bdry p q = bcZ G (boundaryCliqueGraph bdry) p q := by
-- proof
  apply StatMech.IsingFK.wiredFkZ_eq_bcZ G bdry p q

/--
[wiredFkProb_eq_bcProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsLatticeBridge.lean)
-/
@[path]
private lemma wiredFkProb_eq_bcProb_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop) :
-- imply
  wiredFkProb G bdry p q ω = bcProb G (boundaryCliqueGraph bdry) p q ω := by
-- proof
  apply StatMech.IsingFK.wiredFkProb_eq_bcProb G bdry p q ω

/--
[wiredFkPMF_apply_eq_bcProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsLatticeBridge.lean)
-/
@[path]
private lemma wiredFkPMF_apply_eq_bcProb_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (wiredFkPMF G bdry hp hp1 hq) ω = ENNReal.ofReal (bcProb G (boundaryCliqueGraph bdry) p q ω) := by
-- proof
  apply StatMech.IsingFK.wiredFkPMF_apply_eq_bcProb G bdry hp hp1 hq ω


-- created on 2026-10-23
