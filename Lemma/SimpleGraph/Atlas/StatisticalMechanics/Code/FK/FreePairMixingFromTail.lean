import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.FreePairMixingFromTail.Part3
open MeasureTheory Set Filter Function StatMech StatMech.FK


/--
[freeAxisTranslationPower_eq_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreePairMixingFromTail.lean)
-/
@[path]
private lemma freeAxisTranslationPower_eq_pow_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  freeAxisTranslationPower hd n = (freeAxisTranslation hd) ^ n := by
-- proof
  apply StatMech.FK.freeAxisTranslationPower_eq_pow hd n

/--
[shift_freeAxisTranslationPower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreePairMixingFromTail.lean)
-/
@[path]
private lemma shift_freeAxisTranslationPower_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  (shift (freeAxisTranslationPower hd n) : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) = (shift (freeAxisTranslation hd))^[n] := by
-- proof
  apply StatMech.FK.shift_freeAxisTranslationPower hd n

/--
[freeAxisTranslationPower_escape](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreePairMixingFromTail.lean)
-/
@[path]
private lemma freeAxisTranslationPower_escape_eq
  {d : ℕ}
  {F : Finset (Sym2 (Site d))}
  {k : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  ∃ n : ℕ, (↑(F.image (fun e => (freeAxisTranslationPower hd n)⁻¹ • e)) : Set (Sym2 (Site d))) ⊆ (fkTailEdgeWindow d k)ᶜ := by
-- proof
  apply StatMech.FK.freeAxisTranslationPower_escape hd F k

/--
[freeInfiniteVolume_axisShift_ergodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreePairMixingFromTail.lean)
-/
@[path]
private lemma freeInfiniteVolume_axisShift_ergodic_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  _root_.Ergodic (shift (freeAxisTranslation hd) : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) := by
-- proof
  apply StatMech.FK.freeInfiniteVolume_axisShift_ergodic hd hp hp1

/--
[freeInfiniteVolume_pairCorrelationAverage_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreePairMixingFromTail.lean)
-/
@[path]
private lemma freeInfiniteVolume_pairCorrelationAverage_tendsto_eq
  {d : ℕ}
  {p : ℝ}
  {T U : Finset (Sym2 (Site d))}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  let mu := (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, mu.real (fmu_multiOpen T ∩ shift (freeAxisTranslationPower hd k) ⁻¹' fmu_multiOpen U)) atTop (𝓝 (mu.real (fmu_multiOpen T) * mu.real (fmu_multiOpen U))) := by
-- proof
  apply StatMech.FK.freeInfiniteVolume_pairCorrelationAverage_tendsto hd hp hp1 T U

/--
[freeInfiniteVolume_pairMixing_all_parameters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreePairMixingFromTail.lean)
-/
@[path]
private lemma freeInfiniteVolume_pairMixing_all_parameters_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  fmu_PairMixing (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.freeInfiniteVolume_pairMixing_all_parameters hd hp hp1


-- created on 2026-10-23
