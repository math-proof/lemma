import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.TwoDim.NearHalfKKLWire
open MeasureTheory Set Filter Topology StatMech StatMech.TwoDim


/--
[nhkw_nearHalf_kkl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/NearHalfKKLWire.lean)
-/
@[path]
private lemma nhkw_nearHalf_kkl_eq
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {p : ℝ}
  {A : Set (ConfigSpace E)}
  [DecidablePred (· ∈ A)]
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  2 * (StatMech.prob p A * (1 - StatMech.prob p A)) * kklw_logMaxInfl p A ≤ (1 + 2 * (1 - 4 * p * (1 - p)) * (ptn_sigma p) ^ 2 * kklw_logMaxInfl p A) * ∑ e, StatMech.BeffaraDC.influence p A e := by
-- proof
  apply StatMech.TwoDim.nhkw_nearHalf_kkl hp0 hp1 A

/--
[nhkw_hinfl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/NearHalfKKLWire.lean)
-/
@[path]
private lemma nhkw_hinfl_eq
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {A : Set (ConfigSpace E)}
  [DecidablePred (· ∈ A)]
  {q v₀ L : ℝ}
-- given
  (hq1 : q ≤ 1)
  (hv0 : 0 < v₀)
  (hL : 0 < L)
  (hwindow : 2 * (q - 1 / 2) ^ 2 * L ≤ 1)
  (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), v₀ ≤ StatMech.prob p A * (1 - StatMech.prob p A))
  (hlog : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), L ≤ kklw_logMaxInfl p A) :
-- imply
  ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), v₀ * L ≤ ∑ e, StatMech.BeffaraDC.influence p A e := by
-- proof
  apply StatMech.TwoDim.nhkw_hinfl A hq1 hv0 hL hwindow hvar hlog

/--
[nhkw_sharpThreshold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/NearHalfKKLWire.lean)
-/
@[path]
private lemma nhkw_sharpThreshold_eq
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {A : Set (ConfigSpace E)}
  [DecidablePred (· ∈ A)]
  {q v₀ L : ℝ}
-- given
  (hA : IsIncreasing A)
  (hq0 : (1 : ℝ) / 2 ≤ q)
  (hq1 : q ≤ 1)
  (hv0 : 0 < v₀)
  (hL : 0 < L)
  (hwindow : 2 * (q - 1 / 2) ^ 2 * L ≤ 1)
  (hhalf : StatMech.prob (1 / 2) A = 1 / 2)
  (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), v₀ ≤ StatMech.prob p A * (1 - StatMech.prob p A))
  (hlog : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), L ≤ kklw_logMaxInfl p A) :
-- imply
  1 / 2 + (v₀ * L) * (q - 1 / 2) ≤ StatMech.prob q A := by
-- proof
  apply StatMech.TwoDim.nhkw_sharpThreshold A hA hq0 hq1 hv0 hL hwindow hhalf hvar hlog

/--
[nhkw_sharpThreshold_admissible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/NearHalfKKLWire.lean)
-/
@[path]
private lemma nhkw_sharpThreshold_admissible_eq
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {A : Set (ConfigSpace E)}
  [DecidablePred (· ∈ A)]
  {v₀ L ε : ℝ}
-- given
  (hA : IsIncreasing A)
  (hv0 : 0 < v₀)
  (hL : 0 < L)
  (hεhalf : ε < 1 / 2)
  (hq1 : 2 * (1 / 2 - ε) ≤ v₀ * L)
  (hlarge : 2 * (1 / 2 - ε) ^ 2 ≤ v₀ ^ 2 * L)
  (hhalf : StatMech.prob (1 / 2) A = 1 / 2)
  (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) (1 / 2 + (1 / 2 - ε) / (v₀ * L))), v₀ ≤ StatMech.prob p A * (1 - StatMech.prob p A))
  (hlog : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) (1 / 2 + (1 / 2 - ε) / (v₀ * L))), L ≤ kklw_logMaxInfl p A) :
-- imply
  1 - ε ≤ StatMech.prob (1 / 2 + (1 / 2 - ε) / (v₀ * L)) A := by
-- proof
  apply StatMech.TwoDim.nhkw_sharpThreshold_admissible A hA hv0 hL hεhalf hq1 hlarge hhalf hvar hlog

/--
[nhkw_sharpThreshold_of_small_maxInfluence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/NearHalfKKLWire.lean)
-/
@[path]
private lemma nhkw_sharpThreshold_of_small_maxInfluence_eq
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {A : Set (ConfigSpace E)}
  [DecidablePred (· ∈ A)]
  {q v₀ delta : ℝ}
-- given
  (hA : IsIncreasing A)
  (hq0 : (1 : ℝ) / 2 <= q)
  (hq1 : q <= 1)
  (hv0 : 0 < v₀)
  (hdelta0 : 0 < delta)
  (hdelta1 : delta < 1)
  (hwindow : 2 * (q - 1 / 2) ^ 2 * Real.log (1 / delta) <= 1)
  (hhalf : StatMech.prob (1 / 2) A = 1 / 2)
  (hvar : forall p, p ∈ interior (Set.Icc (1 / 2 : ℝ) q) -> v₀ <= StatMech.prob p A * (1 - StatMech.prob p A))
  (hmax : forall p, p ∈ interior (Set.Icc (1 / 2 : ℝ) q) -> maxInfl (OSSS.bernoulliWeight p) (A.indicator (fun _ => (1 : ℝ))) <= delta) :
-- imply
  1 / 2 + (v₀ * Real.log (1 / delta)) * (q - 1 / 2) <= StatMech.prob q A := by
-- proof
  apply StatMech.TwoDim.nhkw_sharpThreshold_of_small_maxInfluence A hA hq0 hq1 hv0 hdelta0 hdelta1 hwindow hhalf hvar hmax


-- created on 2026-10-23
