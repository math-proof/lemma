import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.FiniteEnergy.Part4
open Module SimpleGraph StatMech StatMech.FK


/--
[numClusters_congr_openSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteEnergy.lean)
-/
@[path]
private lemma numClusters_congr_openSub_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ω ω' : ConfigSpace (Sym2 V)}
-- given
  (h : openSub G ω = openSub G ω') :
-- imply
  numClusters G ω = numClusters G ω' := by
-- proof
  apply StatMech.FK.numClusters_congr_openSub G h

/--
[numClusters_setOpen_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteEnergy.lean)
-/
@[path]
private lemma numClusters_setOpen_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : Sym2 V}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  numClusters G (setOpen e ω) ≤ numClusters G (setClosed e ω) := by
-- proof
  apply StatMech.FK.numClusters_setOpen_le G e ω

/--
[numClusters_setClosed_le_setOpen_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteEnergy.lean)
-/
@[path]
private lemma numClusters_setClosed_le_setOpen_succ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : Sym2 V}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  numClusters G (setClosed e ω) ≤ numClusters G (setOpen e ω) + 1 := by
-- proof
  apply StatMech.FK.numClusters_setClosed_le_setOpen_succ G e ω

/--
[openSub_setOpen_eq_setClosed_of_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteEnergy.lean)
-/
@[path]
private lemma openSub_setOpen_eq_setClosed_of_notMem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : Sym2 V}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (he : e ∉ G.edgeFinset) :
-- imply
  openSub G (setOpen e ω) = openSub G (setClosed e ω) := by
-- proof
  apply StatMech.FK.openSub_setOpen_eq_setClosed_of_notMem G he ω

/--
[edgeRest_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteEnergy.lean)
-/
@[path]
private lemma edgeRest_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {e : Sym2 V}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  0 < edgeRest G p e ω := by
-- proof
  apply StatMech.FK.edgeRest_pos G hp hp1 e ω

/--
[edgeProduct_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteEnergy.lean)
-/
@[path]
private lemma edgeProduct_setOpen_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {e : Sym2 V}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (he : e ∈ G.edgeFinset) :
-- imply
  edgeProduct G p (setOpen e ω) = edgeRest G p e ω * p := by
-- proof
  apply StatMech.FK.edgeProduct_setOpen G p he ω

/--
[edgeProduct_setClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteEnergy.lean)
-/
@[path]
private lemma edgeProduct_setClosed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {e : Sym2 V}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (he : e ∈ G.edgeFinset) :
-- imply
  edgeProduct G p (setClosed e ω) = edgeRest G p e ω * (1 - p) := by
-- proof
  apply StatMech.FK.edgeProduct_setClosed G p he ω

/--
[fkWeight_lo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteEnergy.lean)
-/
@[path]
private lemma fkWeight_lo_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {e : Sym2 V}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (he : e ∈ G.edgeFinset) :
-- imply
  (1 - p) * fkWeight G p q (setOpen e ω) ≤ p * fkWeight G p q (setClosed e ω) := by
-- proof
  apply StatMech.FK.fkWeight_lo G hp hp1 hq he ω

/--
[fkWeight_hi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteEnergy.lean)
-/
@[path]
private lemma fkWeight_hi_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {e : Sym2 V}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (he : e ∈ G.edgeFinset) :
-- imply
  p * fkWeight G p q (setClosed e ω) ≤ q * (1 - p) * fkWeight G p q (setOpen e ω) := by
-- proof
  apply StatMech.FK.fkWeight_hi G hp hp1 hq he ω

/--
[condOpen_eq_weightRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteEnergy.lean)
-/
@[path]
private lemma condOpen_eq_weightRatio_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {e : Sym2 V}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  condOpen G p q e ω = fkWeight G p q (setOpen e ω) / (fkWeight G p q (setOpen e ω) + fkWeight G p q (setClosed e ω)) := by
-- proof
  apply StatMech.FK.condOpen_eq_weightRatio G hp hp1 hq e ω

/--
[condOpen_eq_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteEnergy.lean)
-/
@[path]
private lemma condOpen_eq_half_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {e : Sym2 V}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (he : e ∉ G.edgeFinset) :
-- imply
  condOpen G p q e ω = 1 / 2 := by
-- proof
  apply StatMech.FK.condOpen_eq_half G hp hp1 hq he ω

/--
[cFE_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteEnergy.lean)
-/
@[path]
private lemma cFE_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  0 < cFE p q := by
-- proof
  apply StatMech.FK.cFE_pos G hp hp1 hq

/--
[cFE_le_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteEnergy.lean)
-/
@[path]
private lemma cFE_le_half_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  cFE p q ≤ 1 / 2 := by
-- proof
  apply StatMech.FK.cFE_le_half G hp hp1 hq

/--
[finite_energy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteEnergy.lean)
-/
@[path]
private lemma finite_energy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {e : Sym2 V}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  cFE p q ≤ condOpen G p q e ω ∧ condOpen G p q e ω ≤ 1 - cFE p q := by
-- proof
  apply StatMech.FK.finite_energy G hp hp1 hq e ω


-- created on 2026-10-23
