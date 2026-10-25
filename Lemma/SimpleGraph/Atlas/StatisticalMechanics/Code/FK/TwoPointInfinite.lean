import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.TwoPointInfinite.Part5
open MeasureTheory Filter Topology SimpleGraph StatMech StatMech.FK


/--
[bddAbove_range_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointInfinite.lean)
-/
@[path]
private lemma bddAbove_range_apply_eq
  [Countable E]
  {μ : ℕ → ProbabilityMeasure (ConfigSpace E)}
  {A : Set (ConfigSpace E)} :
-- imply
  BddAbove (Set.range (fun n => (μ n) A)) := by
-- proof
  apply StatMech.FK.bddAbove_range_apply μ A

/--
[le_ivTwoPointSup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointInfinite.lean)
-/
@[path]
private lemma le_ivTwoPointSup_eq
  [Countable E]
  {μ : ℕ → ProbabilityMeasure (ConfigSpace E)}
  {A : Set (ConfigSpace E)}
  {n : ℕ} :
-- imply
  (μ n) A ≤ ivTwoPointSup μ A := by
-- proof
  apply StatMech.FK.le_ivTwoPointSup μ A n

/--
[ivTwoPointInf_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointInfinite.lean)
-/
@[path]
private lemma ivTwoPointInf_le_eq
  [Countable E]
  {μ : ℕ → ProbabilityMeasure (ConfigSpace E)}
  {A : Set (ConfigSpace E)}
  {n : ℕ} :
-- imply
  ivTwoPointInf μ A ≤ (μ n) A := by
-- proof
  apply StatMech.FK.ivTwoPointInf_le μ A n

/--
[ivTwoPointSup_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointInfinite.lean)
-/
@[path]
private lemma ivTwoPointSup_pos_eq
  [Countable E]
  {μ : ℕ → ProbabilityMeasure (ConfigSpace E)}
  {A : Set (ConfigSpace E)}
  {n : ℕ}
-- given
  (hn : 0 < (μ n) A) :
-- imply
  0 < ivTwoPointSup μ A := by
-- proof
  apply StatMech.FK.ivTwoPointSup_pos μ A hn

/--
[ivTwoPointInf_pos_of_uniform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointInfinite.lean)
-/
@[path]
private lemma ivTwoPointInf_pos_of_uniform_eq
  [Countable E]
  {μ : ℕ → ProbabilityMeasure (ConfigSpace E)}
  {A : Set (ConfigSpace E)}
  {c : NNReal}
-- given
  (hc : 0 < c)
  (hbound : ∀ n, c ≤ (μ n) A) :
-- imply
  0 < ivTwoPointInf μ A := by
-- proof
  apply StatMech.FK.ivTwoPointInf_pos_of_uniform μ A hc hbound

/--
[ivTwoPointSup_isLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointInfinite.lean)
-/
@[path]
private lemma ivTwoPointSup_isLimit_eq
  [Countable E]
  {μ : ℕ → ProbabilityMeasure (ConfigSpace E)}
  {A : Set (ConfigSpace E)}
-- given
  (hchain : ∀ n, (μ n : Measure (ConfigSpace E)) ≼ (μ (n + 1) : Measure (ConfigSpace E)))
  (hAclopen : IsClopen A)
  (hAinc : IsIncreasing A) :
-- imply
  Tendsto (fun n => (μ n) A) atTop (𝓝 (ivTwoPointSup μ A)) := by
-- proof
  apply StatMech.FK.ivTwoPointSup_isLimit μ hchain hAclopen hAinc

/--
[ivTwoPointInf_isLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointInfinite.lean)
-/
@[path]
private lemma ivTwoPointInf_isLimit_eq
  [Countable E]
  {μ : ℕ → ProbabilityMeasure (ConfigSpace E)}
  {A : Set (ConfigSpace E)}
-- given
  (hchain : ∀ n, (μ (n + 1) : Measure (ConfigSpace E)) ≼ (μ n : Measure (ConfigSpace E)))
  (hAclopen : IsClopen A)
  (hAinc : IsIncreasing A) :
-- imply
  Tendsto (fun n => (μ n) A) atTop (𝓝 (ivTwoPointInf μ A)) := by
-- proof
  apply StatMech.FK.ivTwoPointInf_isLimit μ hchain hAclopen hAinc

/--
[continuous_boxRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointInfinite.lean)
-/
@[path]
private lemma continuous_boxRestrict_eq
  [Countable E]
  {d n : ℕ} :
-- imply
  Continuous (boxRestrict d n) := by
-- proof
  apply StatMech.FK.continuous_boxRestrict d n

/--
[monotone_boxRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointInfinite.lean)
-/
@[path]
private lemma monotone_boxRestrict_eq
  [Countable E]
  {d n : ℕ} :
-- imply
  Monotone (boxRestrict d n) := by
-- proof
  apply StatMech.FK.monotone_boxRestrict d n

/--
[isClopen_boxConnEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointInfinite.lean)
-/
@[path]
private lemma isClopen_boxConnEvent_eq
  [Countable E]
  {d n : ℕ}
  {x y : boxVerts d n} :
-- imply
  IsClopen (boxConnEvent d n x y) := by
-- proof
  apply StatMech.FK.isClopen_boxConnEvent d n x y

/--
[measurableSet_boxConnEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointInfinite.lean)
-/
@[path]
private lemma measurableSet_boxConnEvent_eq
  [Countable E]
  {d n : ℕ}
  {x y : boxVerts d n} :
-- imply
  MeasurableSet (boxConnEvent d n x y) := by
-- proof
  apply StatMech.FK.measurableSet_boxConnEvent d n x y

/--
[isIncreasing_boxConnEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointInfinite.lean)
-/
@[path]
private lemma isIncreasing_boxConnEvent_eq
  [Countable E]
  {d n : ℕ}
  {x y : boxVerts d n} :
-- imply
  IsIncreasing (boxConnEvent d n x y) := by
-- proof
  apply StatMech.FK.isIncreasing_boxConnEvent d n x y

/--
[boxRestrict_extendEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointInfinite.lean)
-/
@[path]
private lemma boxRestrict_extendEdge_eq
  [Countable E]
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))} :
-- imply
  boxRestrict d n (extendEdge d n ω) = ω := by
-- proof
  apply StatMech.FK.boxRestrict_extendEdge d n ω

/--
[extendEdge_preimage_boxConnEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointInfinite.lean)
-/
@[path]
private lemma extendEdge_preimage_boxConnEvent_eq
  [Countable E]
  {d n : ℕ}
  {x y : boxVerts d n} :
-- imply
  extendEdge d n ⁻¹' (boxConnEvent d n x y) = connEvent (boxGraph d n) x y := by
-- proof
  apply StatMech.FK.extendEdge_preimage_boxConnEvent d n x y

/--
[freeFiniteMeasure_real_boxConnEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointInfinite.lean)
-/
@[path]
private lemma freeFiniteMeasure_real_boxConnEvent_eq
  [Countable E]
  {d n : ℕ}
  {p q : ℝ}
  {x y : boxVerts d n}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (freeFiniteMeasure d n hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))).real (boxConnEvent d n x y) = twoPointFun (boxGraph d n) p q x y := by
-- proof
  apply StatMech.FK.freeFiniteMeasure_real_boxConnEvent d n hp hp1 hq x y

/--
[wiredFkProb_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointInfinite.lean)
-/
@[path]
private lemma wiredFkProb_pos_eq
  [Countable E]
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
  0 < wiredFkProb G bdry p q ω := by
-- proof
  apply StatMech.FK.wiredFkProb_pos G bdry hp hp1 hq ω

/--
[wiredFiniteMeasure_real_boxConnEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointInfinite.lean)
-/
@[path]
private lemma wiredFiniteMeasure_real_boxConnEvent_eq
  [Countable E]
  {d n : ℕ}
  {p q : ℝ}
  {x y : boxVerts d n}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (wiredFiniteMeasure d n hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))).real (boxConnEvent d n x y) = ∑ ω : ConfigSpace (Sym2 (boxVerts d n)), (connEvent (boxGraph d n) x y).indicator (fun _ => (1 : ℝ)) ω * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
-- proof
  apply StatMech.FK.wiredFiniteMeasure_real_boxConnEvent d n hp hp1 hq x y

/--
[freeFiniteMeasure_apply_boxConnEvent_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointInfinite.lean)
-/
@[path]
private lemma freeFiniteMeasure_apply_boxConnEvent_pos_eq
  [Countable E]
  {d n : ℕ}
  {p q : ℝ}
  {x y : boxVerts d n}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (h : (boxGraph d n).Reachable x y) :
-- imply
  0 < (freeFiniteMeasure d n hp hp1 hq) (boxConnEvent d n x y) := by
-- proof
  apply StatMech.FK.freeFiniteMeasure_apply_boxConnEvent_pos d n hp hp1 hq h

/--
[wiredFiniteMeasure_apply_boxConnEvent_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointInfinite.lean)
-/
@[path]
private lemma wiredFiniteMeasure_apply_boxConnEvent_pos_eq
  [Countable E]
  {d n : ℕ}
  {p q : ℝ}
  {x y : boxVerts d n}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (h : (boxGraph d n).Reachable x y) :
-- imply
  0 < (wiredFiniteMeasure d n hp hp1 hq) (boxConnEvent d n x y) := by
-- proof
  apply StatMech.FK.wiredFiniteMeasure_apply_boxConnEvent_pos d n hp hp1 hq h

/--
[freeIvTwoPoint_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointInfinite.lean)
-/
@[path]
private lemma freeIvTwoPoint_pos_eq
  [Countable E]
  {d N : ℕ}
  {p q : ℝ}
  {x y : boxVerts d N}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (h : (boxGraph d N).Reachable x y) :
-- imply
  0 < freeIvTwoPoint d N hp hp1 hq x y := by
-- proof
  apply StatMech.FK.freeIvTwoPoint_pos d N hp hp1 hq h

/--
[freeIvTwoPoint_self_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointInfinite.lean)
-/
@[path]
private lemma freeIvTwoPoint_self_pos_eq
  [Countable E]
  {d N : ℕ}
  {p q : ℝ}
  {x : boxVerts d N}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < freeIvTwoPoint d N hp hp1 hq x x := by
-- proof
  apply StatMech.FK.freeIvTwoPoint_self_pos d N hp hp1 hq x

/--
[wiredIvTwoPoint_pos_of_uniform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointInfinite.lean)
-/
@[path]
private lemma wiredIvTwoPoint_pos_of_uniform_eq
  [Countable E]
  {d N : ℕ}
  {p q : ℝ}
  {x y : boxVerts d N}
  {c : NNReal}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hc : 0 < c)
  (hbound : ∀ n, c ≤ (wiredFiniteMeasure d n hp hp1 hq) (boxConnEvent d N x y)) :
-- imply
  0 < wiredIvTwoPoint d N hp hp1 hq x y := by
-- proof
  apply StatMech.FK.wiredIvTwoPoint_pos_of_uniform d N hp hp1 hq hc hbound

/--
[freeIvTwoPoint_isLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointInfinite.lean)
-/
@[path]
private lemma freeIvTwoPoint_isLimit_eq
  [Countable E]
  {d N : ℕ}
  {p q : ℝ}
  {x y : boxVerts d N}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hchain : ∀ n, (freeFiniteMeasure d n hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) ≼ (freeFiniteMeasure d (n + 1) hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d))))) :
-- imply
  Tendsto (fun n => (freeFiniteMeasure d n hp hp1 hq) (boxConnEvent d N x y)) atTop (𝓝 (freeIvTwoPoint d N hp hp1 hq x y)) := by
-- proof
  apply StatMech.FK.freeIvTwoPoint_isLimit d N hp hp1 hq hchain x y

/--
[wiredIvTwoPoint_isLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointInfinite.lean)
-/
@[path]
private lemma wiredIvTwoPoint_isLimit_eq
  [Countable E]
  {d N : ℕ}
  {p q : ℝ}
  {x y : boxVerts d N}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hchain : ∀ n, (wiredFiniteMeasure d (n + 1) hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) ≼ (wiredFiniteMeasure d n hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d))))) :
-- imply
  Tendsto (fun n => (wiredFiniteMeasure d n hp hp1 hq) (boxConnEvent d N x y)) atTop (𝓝 (wiredIvTwoPoint d N hp hp1 hq x y)) := by
-- proof
  apply StatMech.FK.wiredIvTwoPoint_isLimit d N hp hp1 hq hchain x y


-- created on 2026-10-23
