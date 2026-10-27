import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyCertificateExample.Part2
open StatMech StatMech.Exact3D StatMech.Exact3D.BoundedPolymerCase StatMech.Exact3D.BoundedPolymerCase.StableKeyCertificateExample


/--
[rowOfKey_memR_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificateExample.lean)
-/
@[path]
private lemma rowOfKey_memR_zero_eq
  {maxDegree maxRange : ℕ}
  {k : StableKey maxDegree maxRange} :
-- imply
  (rowOfKey k).interval.MemR (0 : ℝ) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyCertificateExample.rowOfKey_memR_zero k

/--
[mem_rowKeyFinset_map_rowOfKey](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificateExample.lean)
-/
@[path]
private lemma mem_rowKeyFinset_map_rowOfKey_eq
  {maxDegree maxRange : ℕ}
  {s : Finset (StableKey maxDegree maxRange)}
  {k : StableKey maxDegree maxRange} :
-- imply
  k ∈ stableKeyIntervalRowKeyFinset (s.toList.map rowOfKey) ↔ k ∈ s := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyCertificateExample.mem_rowKeyFinset_map_rowOfKey s k

/--
[rawRows_exactKeySet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificateExample.lean)
-/
@[path]
private lemma rawRows_exactKeySet_eq
  {d R maxDegree maxRange : ℕ} :
-- imply
  StableKeyIntervalRow.ExactKeySet (rawRows d R maxDegree maxRange) ((exhaustiveTable d R maxDegree maxRange).image stableKey) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyCertificateExample.rawRows_exactKeySet d R maxDegree maxRange

/--
[minimalCubicRows_exactKeySet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificateExample.lean)
-/
@[path]
private lemma minimalCubicRows_exactKeySet_eq
  {d R maxDegree maxRange : ℕ} :
-- imply
  StableKeyIntervalRow.ExactKeySet (minimalCubicRows d R maxDegree maxRange) ((exhaustiveCubicClassTable d R maxDegree maxRange).image minimalCubicStableKey) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyCertificateExample.minimalCubicRows_exactKeySet d R maxDegree maxRange

/--
[rawRows_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificateExample.lean)
-/
@[path]
private lemma rawRows_cover_eq
  {d R maxDegree maxRange : ℕ}
  {c : BoundedPolymerCase d R maxDegree maxRange} :
-- imply
  stableKey c ∈ stableKeyIntervalRowKeyFinset (rawRows d R maxDegree maxRange) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyCertificateExample.rawRows_cover d R maxDegree maxRange c

/--
[minimalCubicRows_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificateExample.lean)
-/
@[path]
private lemma minimalCubicRows_cover_eq
  {d R maxDegree maxRange : ℕ}
  {c : BoundedPolymerCase d R maxDegree maxRange} :
-- imply
  classifyByMinimalCubicStableKey c ∈ stableKeyIntervalRowKeyFinset (minimalCubicRows d R maxDegree maxRange) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyCertificateExample.minimalCubicRows_cover d R maxDegree maxRange c

/--
[rawRows_row_key_mem_generatedKeys](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificateExample.lean)
-/
@[path]
private lemma rawRows_row_key_mem_generatedKeys_eq
  {d R maxDegree maxRange : ℕ}
  {row : StableKeyIntervalRow maxDegree maxRange}
-- given
  (hrow : row ∈ rawRows d R maxDegree maxRange) :
-- imply
  row.key.toKey ∈ (exhaustiveTable d R maxDegree maxRange).image stableKey := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyCertificateExample.rawRows_row_key_mem_generatedKeys d R maxDegree maxRange hrow

/--
[minimalCubicRows_row_key_mem_generatedKeys](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificateExample.lean)
-/
@[path]
private lemma minimalCubicRows_row_key_mem_generatedKeys_eq
  {d R maxDegree maxRange : ℕ}
  {row : StableKeyIntervalRow maxDegree maxRange}
-- given
  (hrow : row ∈ minimalCubicRows d R maxDegree maxRange) :
-- imply
  row.key.toKey ∈ (exhaustiveCubicClassTable d R maxDegree maxRange).image minimalCubicStableKey := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyCertificateExample.minimalCubicRows_row_key_mem_generatedKeys d R maxDegree maxRange hrow

/--
[minimalCubicRows_cover_cubicTransformLocalCoordinate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificateExample.lean)
-/
@[path]
private lemma minimalCubicRows_cover_cubicTransformLocalCoordinate_eq
  {d R maxDegree maxRange : ℕ}
  {c : LocalPolymerCoordinate d}
  {v : Site d}
  {σ : Equiv.Perm (Fin d)}
  {ε : PolymerSupport.CoordinateReflection d}
-- given
  (hbox : c.support.containedInBox R)
  (hbox' : (cubicTransformLocalCoordinate c v σ ε).support.containedInBox R)
  (hdegree : c.degree ≤ maxDegree)
  (hrange : c.range ≤ maxRange) :
-- imply
  classifyByMinimalCubicStableKey (ofLocalCoordinate (cubicTransformLocalCoordinate c v σ ε) hbox' (by simpa using hdegree) (by simpa using hrange)) ∈ stableKeyIntervalRowKeyFinset (minimalCubicRows d R maxDegree maxRange) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyCertificateExample.minimalCubicRows_cover_cubicTransformLocalCoordinate c v σ ε hbox hbox' hdegree hrange

/--
[rawRows_row_sound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificateExample.lean)
-/
@[path]
private lemma rawRows_row_sound_eq
  {d R maxDegree maxRange : ℕ}
  {row : StableKeyIntervalRow maxDegree maxRange}
-- given
  (hrow : row ∈ rawRows d R maxDegree maxRange) :
-- imply
  row.interval.MemR (0 : ℝ) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyCertificateExample.rawRows_row_sound d R maxDegree maxRange row hrow

/--
[minimalCubicRows_row_sound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificateExample.lean)
-/
@[path]
private lemma minimalCubicRows_row_sound_eq
  {d R maxDegree maxRange : ℕ}
  {row : StableKeyIntervalRow maxDegree maxRange}
-- given
  (hrow : row ∈ minimalCubicRows d R maxDegree maxRange) :
-- imply
  row.interval.MemR (0 : ℝ) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyCertificateExample.minimalCubicRows_row_sound d R maxDegree maxRange row hrow

/--
[rawRows_zero_covers_and_sound_boundedLocal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificateExample.lean)
-/
@[path]
private lemma rawRows_zero_covers_and_sound_boundedLocal_eq
  {d R maxDegree maxRange : ℕ} :
-- imply
  RatInterval.CaseTable.Covers (externalStableKeyIntervalRowTable (rawRows d R maxDegree maxRange) zeroInterval) (fun c : BoundedLocalCoordinate d R maxDegree maxRange => stableKey (classifyBoundedLocalCoordinate c)) ∧ RatInterval.CaseTable.Sound (externalStableKeyIntervalRowTable (rawRows d R maxDegree maxRange) zeroInterval) (fun c : BoundedLocalCoordinate d R maxDegree maxRange => stableKey (classifyBoundedLocalCoordinate c)) (fun _ => (0 : ℝ)) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyCertificateExample.rawRows_zero_covers_and_sound_boundedLocal d R maxDegree maxRange

/--
[minimalCubicRows_zero_covers_and_sound_boundedLocal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificateExample.lean)
-/
@[path]
private lemma minimalCubicRows_zero_covers_and_sound_boundedLocal_eq
  {d R maxDegree maxRange : ℕ} :
-- imply
  RatInterval.CaseTable.Covers (externalStableKeyIntervalRowTable (minimalCubicRows d R maxDegree maxRange) zeroInterval) (fun c : BoundedLocalCoordinate d R maxDegree maxRange => classifyByMinimalCubicStableKey (classifyBoundedLocalCoordinate c)) ∧ RatInterval.CaseTable.Sound (externalStableKeyIntervalRowTable (minimalCubicRows d R maxDegree maxRange) zeroInterval) (fun c : BoundedLocalCoordinate d R maxDegree maxRange => classifyByMinimalCubicStableKey (classifyBoundedLocalCoordinate c)) (fun _ => (0 : ℝ)) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyCertificateExample.minimalCubicRows_zero_covers_and_sound_boundedLocal d R maxDegree maxRange


-- created on 2026-10-23
