import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
open MeasureTheory StatMech StatMech.FK


/--
[wiredFkWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteVolume.lean)
-/
@[path]
private lemma wiredFkWeight_pos_eq
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
  0 < wiredFkWeight G bdry p q ω := by
-- proof
  apply StatMech.FK.wiredFkWeight_pos G bdry hp hp1 hq ω

/--
[wiredFkWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteVolume.lean)
-/
@[path]
private lemma wiredFkWeight_nonneg_eq
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
  0 ≤ wiredFkWeight G bdry p q ω := by
-- proof
  apply StatMech.FK.wiredFkWeight_nonneg G bdry hp hp1 hq ω

/--
[wiredFkZ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteVolume.lean)
-/
@[path]
private lemma wiredFkZ_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {p q : ℝ}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < wiredFkZ G bdry p q := by
-- proof
  apply StatMech.FK.wiredFkZ_pos G bdry hp hp1 hq

/--
[wiredFkZ_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteVolume.lean)
-/
@[path]
private lemma wiredFkZ_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {p q : ℝ}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  wiredFkZ G bdry p q ≠ 0 := by
-- proof
  apply StatMech.FK.wiredFkZ_ne_zero G bdry hp hp1 hq

/--
[wiredFkProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteVolume.lean)
-/
@[path]
private lemma wiredFkProb_nonneg_eq
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
  0 ≤ wiredFkProb G bdry p q ω := by
-- proof
  apply StatMech.FK.wiredFkProb_nonneg G bdry hp hp1 hq ω

/--
[wiredFkProb_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteVolume.lean)
-/
@[path]
private lemma wiredFkProb_sum_eq_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {p q : ℝ}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ∑ ω : ConfigSpace (Sym2 V), wiredFkProb G bdry p q ω = 1 := by
-- proof
  apply StatMech.FK.wiredFkProb_sum_eq_one G bdry hp hp1 hq

/--
[edgeIncl_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteVolume.lean)
-/
@[path]
private lemma edgeIncl_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d n : ℕ}
-- given
  (bdry : V → Prop) :
-- imply
  Function.Injective (edgeIncl d n) := by
-- proof
  apply StatMech.FK.edgeIncl_injective G bdry d n

/--
[measurable_extendEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteVolume.lean)
-/
@[path]
private lemma measurable_extendEdge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d n : ℕ}
-- given
  (bdry : V → Prop) :
-- imply
  Measurable (extendEdge d n) := by
-- proof
  apply StatMech.FK.measurable_extendEdge G bdry d n

/--
[freeInfiniteVolume_isLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteVolume.lean)
-/
@[path]
private lemma freeInfiniteVolume_isLimit_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d : ℕ}
  {p q : ℝ}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ WeakConvergesTo (fun n => freeFiniteMeasure d (φ n) hp hp1 hq) (freeInfiniteVolume d hp hp1 hq) := by
-- proof
  apply StatMech.FK.freeInfiniteVolume_isLimit G bdry d hp hp1 hq

/--
[wiredInfiniteVolume_isLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteVolume.lean)
-/
@[path]
private lemma wiredInfiniteVolume_isLimit_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d : ℕ}
  {p q : ℝ}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ WeakConvergesTo (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq) (wiredInfiniteVolume d hp hp1 hq) := by
-- proof
  apply StatMech.FK.wiredInfiniteVolume_isLimit G bdry d hp hp1 hq


-- created on 2026-10-23
