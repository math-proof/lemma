import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityFKBridge
open MeasureTheory Set StatMech StatMech.FrontierB


/--
[esWeight_open_sum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityFKBridge.lean)
-/
@[path]
private lemma esWeight_open_sum_eq_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {p : ℝ}
  {sigma : V → Fin q}
  {target : Sym2 V}
-- given
  (htarget : target ∈ G.edgeFinset) :
-- imply
  (∑ omega : ConfigSpace (Sym2 V), esWeight G p sigma omega * (if omega target then 1 else 0)) = p * monoIndicator sigma target * ∑ omega : ConfigSpace (Sym2 V), esWeight G p sigma omega := by
-- proof
  apply StatMech.FrontierB.esWeight_open_sum_eq G q p sigma target htarget

/--
[edgeMargProb_fkProb_eq_p_mul_esMono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityFKBridge.lean)
-/
@[path]
private lemma edgeMargProb_fkProb_eq_p_mul_esMono_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {p : ℝ}
  {target : Sym2 V}
-- given
  (htarget : target ∈ G.edgeFinset) :
-- imply
  edgeMargProb (fkProb G p (q : ℝ)) target = p * ∑ sigma : V → Fin q, esFirstMarginal G q p sigma * monoIndicator sigma target := by
-- proof
  apply StatMech.FrontierB.edgeMargProb_fkProb_eq_p_mul_esMono G q p target htarget

/--
[freeInfiniteVolume_eq_wiredInfiniteVolume_of_edgeDensity_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityFKBridge.lean)
-/
@[path]
private lemma freeInfiniteVolume_eq_wiredInfiniteVolume_of_edgeDensity_eq_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hdens : ∀ (N : ℕ) (e : Sym2 (boxVerts d N)), freeEdgeDensity d 2 (edgeIncl d N e) p = wiredEdgeDensity d 2 (edgeIncl d N e) p) :
-- imply
  (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) = (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FrontierB.freeInfiniteVolume_eq_wiredInfiniteVolume_of_edgeDensity_eq hp hp1 hdens


-- created on 2026-10-23
