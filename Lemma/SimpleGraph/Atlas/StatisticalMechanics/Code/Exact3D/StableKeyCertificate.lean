import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyCertificate.Part10
open StatMech StatMech.Exact3D StatMech.Exact3D.BoundedPolymerCase StatMech.Exact3D.BoundedPolymerCase.StableKeyRecord StatMech.Exact3D.BoundedPolymerCase.ValidStableKeyRecord StatMech.Exact3D.BoundedPolymerCase.StableKeyIntervalRow


/--
[ofKey_degree_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma ofKey_degree_le_eq
  {maxDegree maxRange : ℕ}
  {k : StableKey maxDegree maxRange} :
-- imply
  (ofKey k).degree ≤ maxDegree := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyRecord.ofKey_degree_le k

/--
[ofKey_range_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma ofKey_range_le_eq
  {maxDegree maxRange : ℕ}
  {k : StableKey maxDegree maxRange} :
-- imply
  (ofKey k).range ≤ maxRange := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyRecord.ofKey_range_le k

/--
[ofKey_stableKey_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma ofKey_stableKey_support_eq
  {d R maxDegree maxRange : ℕ}
  {c : BoundedPolymerCase d R maxDegree maxRange} :
-- imply
  (ofKey (stableKey c)).support = supportKey c.support := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyRecord.ofKey_stableKey_support c

/--
[ofKey_stableKey_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma ofKey_stableKey_degree_eq
  {d R maxDegree maxRange : ℕ}
  {c : BoundedPolymerCase d R maxDegree maxRange} :
-- imply
  (ofKey (stableKey c)).degree = c.degree := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyRecord.ofKey_stableKey_degree c

/--
[ofKey_stableKey_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma ofKey_stableKey_range_eq
  {d R maxDegree maxRange : ℕ}
  {c : BoundedPolymerCase d R maxDegree maxRange} :
-- imply
  (ofKey (stableKey c)).range = c.range := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyRecord.ofKey_stableKey_range c

/--
[toKey_ofKey](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma toKey_ofKey_eq
  {maxDegree maxRange : ℕ}
  {k : StableKey maxDegree maxRange} :
-- imply
  (ofKey k).toKey (ofKey_degree_le k) (ofKey_range_le k) = k := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyRecord.toKey_ofKey k

/--
[ofKey_toKey](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma ofKey_toKey_eq
  {maxDegree maxRange : ℕ}
  {r : StableKeyRecord}
-- given
  (hdegree : r.degree ≤ maxDegree)
  (hrange : r.range ≤ maxRange) :
-- imply
  ofKey (r.toKey hdegree hrange) = r := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyRecord.ofKey_toKey r hdegree hrange

/--
[toKey_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma toKey_mk_eq
  {maxDegree maxRange : ℕ}
  {record : StableKeyRecord}
-- given
  (degree_le : record.degree ≤ maxDegree)
  (range_le : record.range ≤ maxRange) :
-- imply
  toKey (ValidStableKeyRecord.mk record degree_le range_le) = record.toKey degree_le range_le := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.ValidStableKeyRecord.toKey_mk record degree_le range_le

/--
[toKey_ofKey](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma toKey_ofKey_eq_2
  {maxDegree maxRange : ℕ}
  {k : StableKey maxDegree maxRange} :
-- imply
  (ofKey k).toKey = k := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.ValidStableKeyRecord.toKey_ofKey k

/--
[validRecordKeyFinset_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma validRecordKeyFinset_nil_eq
  {maxDegree maxRange : ℕ} :
-- imply
  validRecordKeyFinset ([] : List (ValidStableKeyRecord maxDegree maxRange)) = ∅ := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.validRecordKeyFinset_nil

/--
[mem_validRecordKeyFinset_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma mem_validRecordKeyFinset_cons_eq
  {maxDegree maxRange : ℕ}
  {record : ValidStableKeyRecord maxDegree maxRange}
  {records : List (ValidStableKeyRecord maxDegree maxRange)}
  {k : StableKey maxDegree maxRange} :
-- imply
  k ∈ validRecordKeyFinset (record :: records) ↔ record.toKey = k ∨ k ∈ validRecordKeyFinset records := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.mem_validRecordKeyFinset_cons record records k

/--
[externalStableKeyIntervalTable_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma externalStableKeyIntervalTable_cases_eq
  {maxDegree maxRange : ℕ}
  {records : List (ValidStableKeyRecord maxDegree maxRange)}
  {intervalOf : StableKey maxDegree maxRange → RatInterval} :
-- imply
  (externalStableKeyIntervalTable records intervalOf).cases = validRecordKeyFinset records := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.externalStableKeyIntervalTable_cases records intervalOf

/--
[externalStableKeyIntervalTable_interval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma externalStableKeyIntervalTable_interval_eq
  {maxDegree maxRange : ℕ}
  {records : List (ValidStableKeyRecord maxDegree maxRange)}
  {intervalOf : StableKey maxDegree maxRange → RatInterval}
  {k : StableKey maxDegree maxRange} :
-- imply
  (externalStableKeyIntervalTable records intervalOf).interval k = intervalOf k := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.externalStableKeyIntervalTable_interval records intervalOf k

/--
[externalStableKeyIntervalTable_covers_and_sound_of_keyValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma externalStableKeyIntervalTable_covers_and_sound_of_keyValue_eq
  {maxDegree maxRange : ℕ}
  {records : List (ValidStableKeyRecord maxDegree maxRange)}
  {intervalOf : StableKey maxDegree maxRange → RatInterval}
  {classifier : α → StableKey maxDegree maxRange}
  {value : α → ℝ}
  {keyValue : StableKey maxDegree maxRange → ℝ}
-- given
  (hcover : ∀ a, classifier a ∈ validRecordKeyFinset records)
  (hvalue : ∀ a, value a = keyValue (classifier a))
  (hkey : ∀ k, k ∈ validRecordKeyFinset records → (intervalOf k).MemR (keyValue k)) :
-- imply
  RatInterval.CaseTable.Covers (externalStableKeyIntervalTable records intervalOf) classifier ∧ RatInterval.CaseTable.Sound (externalStableKeyIntervalTable records intervalOf) classifier value := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.externalStableKeyIntervalTable_covers_and_sound_of_keyValue records intervalOf classifier value keyValue hcover hvalue hkey

/--
[mem_stableKeyIntervalRowKeyFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma mem_stableKeyIntervalRowKeyFinset_eq
  {maxDegree maxRange : ℕ}
  {rows : List (StableKeyIntervalRow maxDegree maxRange)}
  {k : StableKey maxDegree maxRange} :
-- imply
  k ∈ stableKeyIntervalRowKeyFinset rows ↔ ∃ row, row ∈ rows ∧ row.key.toKey = k := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.mem_stableKeyIntervalRowKeyFinset rows k

/--
[ofKeyInterval_key_toKey](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma ofKeyInterval_key_toKey_eq
  {maxDegree maxRange : ℕ}
  {intervalOf : StableKey maxDegree maxRange → RatInterval}
  {k : StableKey maxDegree maxRange} :
-- imply
  (ofKeyInterval intervalOf k).key.toKey = k := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyIntervalRow.ofKeyInterval_key_toKey intervalOf k

/--
[ofKeyInterval_interval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma ofKeyInterval_interval_eq
  {maxDegree maxRange : ℕ}
  {intervalOf : StableKey maxDegree maxRange → RatInterval}
  {k : StableKey maxDegree maxRange} :
-- imply
  (ofKeyInterval intervalOf k).interval = intervalOf k := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyIntervalRow.ofKeyInterval_interval intervalOf k

/--
[ofKey_key_toKey](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma ofKey_key_toKey_eq
  {maxDegree maxRange : ℕ}
  {intervalOf : StableKey maxDegree maxRange → RatInterval}
  {k : StableKey maxDegree maxRange} :
-- imply
  (ofKey intervalOf k).key.toKey = k := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyIntervalRow.ofKey_key_toKey intervalOf k

/--
[ofKey_interval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma ofKey_interval_eq
  {maxDegree maxRange : ℕ}
  {intervalOf : StableKey maxDegree maxRange → RatInterval}
  {k : StableKey maxDegree maxRange} :
-- imply
  (ofKey intervalOf k).interval = intervalOf k := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyIntervalRow.ofKey_interval intervalOf k

/--
[mem_keyFinset_map_ofKeyInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma mem_keyFinset_map_ofKeyInterval_eq
  {maxDegree maxRange : ℕ}
  {s : Finset (StableKey maxDegree maxRange)}
  {intervalOf : StableKey maxDegree maxRange → RatInterval}
  {k : StableKey maxDegree maxRange} :
-- imply
  k ∈ stableKeyIntervalRowKeyFinset (s.toList.map (ofKeyInterval intervalOf)) ↔ k ∈ s := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyIntervalRow.mem_keyFinset_map_ofKeyInterval s intervalOf k

/--
[mem_keyFinset_rowsOfKeys](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma mem_keyFinset_rowsOfKeys_eq
  {maxDegree maxRange : ℕ}
  {s : Finset (StableKey maxDegree maxRange)}
  {intervalOf : StableKey maxDegree maxRange → RatInterval}
  {k : StableKey maxDegree maxRange} :
-- imply
  k ∈ stableKeyIntervalRowKeyFinset (rowsOfKeys s intervalOf) ↔ k ∈ s := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyIntervalRow.mem_keyFinset_rowsOfKeys s intervalOf k

/--
[interval_eq_of_mem_map_ofKeyInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma interval_eq_of_mem_map_ofKeyInterval_eq
  {maxDegree maxRange : ℕ}
  {s : Finset (StableKey maxDegree maxRange)}
  {intervalOf : StableKey maxDegree maxRange → RatInterval}
  {row : StableKeyIntervalRow maxDegree maxRange}
-- given
  (hrow : row ∈ s.toList.map (ofKeyInterval intervalOf)) :
-- imply
  row.interval = intervalOf row.key.toKey := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyIntervalRow.interval_eq_of_mem_map_ofKeyInterval s intervalOf hrow

/--
[interval_eq_of_mem_rowsOfKeys](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma interval_eq_of_mem_rowsOfKeys_eq
  {maxDegree maxRange : ℕ}
  {s : Finset (StableKey maxDegree maxRange)}
  {intervalOf : StableKey maxDegree maxRange → RatInterval}
  {row : StableKeyIntervalRow maxDegree maxRange}
-- given
  (hrow : row ∈ rowsOfKeys s intervalOf) :
-- imply
  row.interval = intervalOf row.key.toKey := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyIntervalRow.interval_eq_of_mem_rowsOfKeys s intervalOf hrow

/--
[memR_of_mem_map_ofKeyInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma memR_of_mem_map_ofKeyInterval_eq
  {maxDegree maxRange : ℕ}
  {s : Finset (StableKey maxDegree maxRange)}
  {intervalOf : StableKey maxDegree maxRange → RatInterval}
  {keyValue : StableKey maxDegree maxRange → ℝ}
  {row : StableKeyIntervalRow maxDegree maxRange}
-- given
  (hmem : ∀ k, k ∈ s → (intervalOf k).MemR (keyValue k))
  (hrow : row ∈ s.toList.map (ofKeyInterval intervalOf)) :
-- imply
  row.interval.MemR (keyValue row.key.toKey) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyIntervalRow.memR_of_mem_map_ofKeyInterval s intervalOf keyValue hmem hrow

/--
[memR_of_mem_rowsOfKeys](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma memR_of_mem_rowsOfKeys_eq
  {maxDegree maxRange : ℕ}
  {s : Finset (StableKey maxDegree maxRange)}
  {intervalOf : StableKey maxDegree maxRange → RatInterval}
  {keyValue : StableKey maxDegree maxRange → ℝ}
  {row : StableKeyIntervalRow maxDegree maxRange}
-- given
  (hmem : ∀ k, k ∈ s → (intervalOf k).MemR (keyValue k))
  (hrow : row ∈ rowsOfKeys s intervalOf) :
-- imply
  row.interval.MemR (keyValue row.key.toKey) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyIntervalRow.memR_of_mem_rowsOfKeys s intervalOf keyValue hmem hrow

/--
[upper_le_of_mem_map_ofKeyInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma upper_le_of_mem_map_ofKeyInterval_eq
  {maxDegree maxRange : ℕ}
  {s : Finset (StableKey maxDegree maxRange)}
  {intervalOf : StableKey maxDegree maxRange → RatInterval}
  {bound : ℝ}
  {row : StableKeyIntervalRow maxDegree maxRange}
-- given
  (hupper : ∀ k, k ∈ s → (((intervalOf k).upper : ℚ) : ℝ) ≤ bound)
  (hrow : row ∈ s.toList.map (ofKeyInterval intervalOf)) :
-- imply
  ((row.interval.upper : ℚ) : ℝ) ≤ bound := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyIntervalRow.upper_le_of_mem_map_ofKeyInterval s intervalOf hupper hrow

/--
[upper_le_of_mem_rowsOfKeys](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma upper_le_of_mem_rowsOfKeys_eq
  {maxDegree maxRange : ℕ}
  {s : Finset (StableKey maxDegree maxRange)}
  {intervalOf : StableKey maxDegree maxRange → RatInterval}
  {bound : ℝ}
  {row : StableKeyIntervalRow maxDegree maxRange}
-- given
  (hupper : ∀ k, k ∈ s → (((intervalOf k).upper : ℚ) : ℝ) ≤ bound)
  (hrow : row ∈ rowsOfKeys s intervalOf) :
-- imply
  ((row.interval.upper : ℚ) : ℝ) ≤ bound := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyIntervalRow.upper_le_of_mem_rowsOfKeys s intervalOf hupper hrow

/--
[exactKeySet_map_ofKeyInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma exactKeySet_map_ofKeyInterval_eq
  {maxDegree maxRange : ℕ}
  {s : Finset (StableKey maxDegree maxRange)}
  {intervalOf : StableKey maxDegree maxRange → RatInterval} :
-- imply
  ExactKeySet (s.toList.map (ofKeyInterval intervalOf)) s := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyIntervalRow.exactKeySet_map_ofKeyInterval s intervalOf

/--
[exactKeySet_rowsOfKeys](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma exactKeySet_rowsOfKeys_eq
  {maxDegree maxRange : ℕ}
  {s : Finset (StableKey maxDegree maxRange)}
  {intervalOf : StableKey maxDegree maxRange → RatInterval} :
-- imply
  ExactKeySet (rowsOfKeys s intervalOf) s := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyIntervalRow.exactKeySet_rowsOfKeys s intervalOf

/--
[exactKeySet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma exactKeySet_iff_eq
  {maxDegree maxRange : ℕ}
  {rows : List (StableKeyIntervalRow maxDegree maxRange)}
  {expected : Finset (StableKey maxDegree maxRange)} :
-- imply
  ExactKeySet rows expected ↔ ∀ k, k ∈ stableKeyIntervalRowKeyFinset rows ↔ k ∈ expected := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyIntervalRow.exactKeySet_iff

/--
[mem_expected_of_exactKeySet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma mem_expected_of_exactKeySet_eq
  {maxDegree maxRange : ℕ}
  {rows : List (StableKeyIntervalRow maxDegree maxRange)}
  {expected : Finset (StableKey maxDegree maxRange)}
  {k : StableKey maxDegree maxRange}
-- given
  (h : ExactKeySet rows expected)
  (hk : k ∈ stableKeyIntervalRowKeyFinset rows) :
-- imply
  k ∈ expected := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyIntervalRow.mem_expected_of_exactKeySet h hk

/--
[mem_rows_of_exactKeySet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma mem_rows_of_exactKeySet_eq
  {maxDegree maxRange : ℕ}
  {rows : List (StableKeyIntervalRow maxDegree maxRange)}
  {expected : Finset (StableKey maxDegree maxRange)}
  {k : StableKey maxDegree maxRange}
-- given
  (h : ExactKeySet rows expected)
  (hk : k ∈ expected) :
-- imply
  k ∈ stableKeyIntervalRowKeyFinset rows := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyIntervalRow.mem_rows_of_exactKeySet h hk

/--
[row_key_mem_expected_of_exactKeySet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma row_key_mem_expected_of_exactKeySet_eq
  {maxDegree maxRange : ℕ}
  {rows : List (StableKeyIntervalRow maxDegree maxRange)}
  {expected : Finset (StableKey maxDegree maxRange)}
  {row : StableKeyIntervalRow maxDegree maxRange}
-- given
  (h : ExactKeySet rows expected)
  (hrow : row ∈ rows) :
-- imply
  row.key.toKey ∈ expected := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyIntervalRow.row_key_mem_expected_of_exactKeySet h hrow

/--
[classifier_mem_rows_of_exactKeySet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma classifier_mem_rows_of_exactKeySet_eq
  {maxDegree maxRange : ℕ}
  {rows : List (StableKeyIntervalRow maxDegree maxRange)}
  {expected : Finset (StableKey maxDegree maxRange)}
  {classifier : α → StableKey maxDegree maxRange}
  {a : α}
-- given
  (h : ExactKeySet rows expected)
  (hclassifier : ∀ a, classifier a ∈ expected) :
-- imply
  classifier a ∈ stableKeyIntervalRowKeyFinset rows := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyIntervalRow.classifier_mem_rows_of_exactKeySet h classifier hclassifier a

/--
[stableKeyIntervalRowKeyFinset_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma stableKeyIntervalRowKeyFinset_nil_eq
  {maxDegree maxRange : ℕ} :
-- imply
  stableKeyIntervalRowKeyFinset ([] : List (StableKeyIntervalRow maxDegree maxRange)) = ∅ := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.stableKeyIntervalRowKeyFinset_nil

/--
[mem_stableKeyIntervalRowKeyFinset_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma mem_stableKeyIntervalRowKeyFinset_cons_eq
  {maxDegree maxRange : ℕ}
  {row : StableKeyIntervalRow maxDegree maxRange}
  {rows : List (StableKeyIntervalRow maxDegree maxRange)}
  {k : StableKey maxDegree maxRange} :
-- imply
  k ∈ stableKeyIntervalRowKeyFinset (row :: rows) ↔ row.key.toKey = k ∨ k ∈ stableKeyIntervalRowKeyFinset rows := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.mem_stableKeyIntervalRowKeyFinset_cons row rows k

/--
[intervalOfRows_eq_fallback_of_not_mem_keyFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma intervalOfRows_eq_fallback_of_not_mem_keyFinset_eq
  {maxDegree maxRange : ℕ}
  {rows : List (StableKeyIntervalRow maxDegree maxRange)}
  {fallback : RatInterval}
  {k : StableKey maxDegree maxRange}
-- given
  (hk : k ∉ stableKeyIntervalRowKeyFinset rows) :
-- imply
  intervalOfRows rows fallback k = fallback := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.intervalOfRows_eq_fallback_of_not_mem_keyFinset rows fallback hk

/--
[exists_row_intervalOfRows_eq_of_mem_keyFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma exists_row_intervalOfRows_eq_of_mem_keyFinset_eq
  {maxDegree maxRange : ℕ}
  {rows : List (StableKeyIntervalRow maxDegree maxRange)}
  {fallback : RatInterval}
  {k : StableKey maxDegree maxRange}
-- given
  (hk : k ∈ stableKeyIntervalRowKeyFinset rows) :
-- imply
  ∃ row, row ∈ rows ∧ row.key.toKey = k ∧ intervalOfRows rows fallback k = row.interval := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.exists_row_intervalOfRows_eq_of_mem_keyFinset rows fallback hk

/--
[intervalOfRows_memR_of_mem_keyFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma intervalOfRows_memR_of_mem_keyFinset_eq
  {maxDegree maxRange : ℕ}
  {rows : List (StableKeyIntervalRow maxDegree maxRange)}
  {fallback : RatInterval}
  {keyValue : StableKey maxDegree maxRange → ℝ}
  {k : StableKey maxDegree maxRange}
-- given
  (hrow : ∀ row, row ∈ rows → row.interval.MemR (keyValue row.key.toKey))
  (hk : k ∈ stableKeyIntervalRowKeyFinset rows) :
-- imply
  (intervalOfRows rows fallback k).MemR (keyValue k) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.intervalOfRows_memR_of_mem_keyFinset rows fallback keyValue hrow hk

/--
[externalStableKeyIntervalRowTable_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma externalStableKeyIntervalRowTable_cases_eq
  {maxDegree maxRange : ℕ}
  {rows : List (StableKeyIntervalRow maxDegree maxRange)}
  {fallback : RatInterval} :
-- imply
  (externalStableKeyIntervalRowTable rows fallback).cases = stableKeyIntervalRowKeyFinset rows := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.externalStableKeyIntervalRowTable_cases rows fallback

/--
[externalStableKeyIntervalRowTable_interval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma externalStableKeyIntervalRowTable_interval_eq
  {maxDegree maxRange : ℕ}
  {rows : List (StableKeyIntervalRow maxDegree maxRange)}
  {fallback : RatInterval}
  {k : StableKey maxDegree maxRange} :
-- imply
  (externalStableKeyIntervalRowTable rows fallback).interval k = intervalOfRows rows fallback k := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.externalStableKeyIntervalRowTable_interval rows fallback k

/--
[externalStableKeyIntervalRowTable_covers_and_sound_of_keyValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma externalStableKeyIntervalRowTable_covers_and_sound_of_keyValue_eq
  {maxDegree maxRange : ℕ}
  {rows : List (StableKeyIntervalRow maxDegree maxRange)}
  {fallback : RatInterval}
  {classifier : α → StableKey maxDegree maxRange}
  {value : α → ℝ}
  {keyValue : StableKey maxDegree maxRange → ℝ}
-- given
  (hcover : ∀ a, classifier a ∈ stableKeyIntervalRowKeyFinset rows)
  (hvalue : ∀ a, value a = keyValue (classifier a))
  (hrow : ∀ row, row ∈ rows → row.interval.MemR (keyValue row.key.toKey)) :
-- imply
  RatInterval.CaseTable.Covers (externalStableKeyIntervalRowTable rows fallback) classifier ∧ RatInterval.CaseTable.Sound (externalStableKeyIntervalRowTable rows fallback) classifier value := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.externalStableKeyIntervalRowTable_covers_and_sound_of_keyValue rows fallback classifier value keyValue hcover hvalue hrow

/--
[externalStableKeyIntervalRowTable_covers_and_sound_of_exactKeySet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma externalStableKeyIntervalRowTable_covers_and_sound_of_exactKeySet_eq
  {maxDegree maxRange : ℕ}
  {rows : List (StableKeyIntervalRow maxDegree maxRange)}
  {fallback : RatInterval}
  {expected : Finset (StableKey maxDegree maxRange)}
  {classifier : α → StableKey maxDegree maxRange}
  {value : α → ℝ}
  {keyValue : StableKey maxDegree maxRange → ℝ}
-- given
  (hexact : StableKeyIntervalRow.ExactKeySet rows expected)
  (hcover : ∀ a, classifier a ∈ expected)
  (hvalue : ∀ a, value a = keyValue (classifier a))
  (hrow : ∀ row, row ∈ rows → row.interval.MemR (keyValue row.key.toKey)) :
-- imply
  RatInterval.CaseTable.Covers (externalStableKeyIntervalRowTable rows fallback) classifier ∧ RatInterval.CaseTable.Sound (externalStableKeyIntervalRowTable rows fallback) classifier value := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.externalStableKeyIntervalRowTable_covers_and_sound_of_exactKeySet rows fallback expected classifier value keyValue hexact hcover hvalue hrow

/--
[externalStableKeyIntervalRows_covers_and_sound_boundedLocal_of_keyValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma externalStableKeyIntervalRows_covers_and_sound_boundedLocal_of_keyValue_eq
  {d R maxDegree maxRange : ℕ}
  {rows : List (StableKeyIntervalRow maxDegree maxRange)}
  {fallback : RatInterval}
  {value : BoundedLocalCoordinate d R maxDegree maxRange → ℝ}
  {keyValue : StableKey maxDegree maxRange → ℝ}
-- given
  (hcover : ∀ c : BoundedPolymerCase d R maxDegree maxRange, stableKey c ∈ stableKeyIntervalRowKeyFinset rows)
  (hvalue : ∀ c, value c = keyValue (stableKey (classifyBoundedLocalCoordinate c)))
  (hrow : ∀ row, row ∈ rows → row.interval.MemR (keyValue row.key.toKey)) :
-- imply
  RatInterval.CaseTable.Covers (externalStableKeyIntervalRowTable rows fallback) (fun c : BoundedLocalCoordinate d R maxDegree maxRange => stableKey (classifyBoundedLocalCoordinate c)) ∧ RatInterval.CaseTable.Sound (externalStableKeyIntervalRowTable rows fallback) (fun c : BoundedLocalCoordinate d R maxDegree maxRange => stableKey (classifyBoundedLocalCoordinate c)) value := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.externalStableKeyIntervalRows_covers_and_sound_boundedLocal_of_keyValue rows fallback value keyValue hcover hvalue hrow

/--
[externalStableKeyIntervalRows_covers_and_sound_minimalCubicBoundedLocal_of_keyValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean)
-/
@[path]
private lemma externalStableKeyIntervalRows_covers_and_sound_minimalCubicBoundedLocal_of_keyValue_eq
  {d R maxDegree maxRange : ℕ}
  {rows : List (StableKeyIntervalRow maxDegree maxRange)}
  {fallback : RatInterval}
  {value : BoundedLocalCoordinate d R maxDegree maxRange → ℝ}
  {keyValue : StableKey maxDegree maxRange → ℝ}
-- given
  (hcover : ∀ c : BoundedPolymerCase d R maxDegree maxRange, classifyByMinimalCubicStableKey c ∈ stableKeyIntervalRowKeyFinset rows)
  (hvalue : ∀ c, value c = keyValue (classifyByMinimalCubicStableKey (classifyBoundedLocalCoordinate c)))
  (hrow : ∀ row, row ∈ rows → row.interval.MemR (keyValue row.key.toKey)) :
-- imply
  RatInterval.CaseTable.Covers (externalStableKeyIntervalRowTable rows fallback) (fun c : BoundedLocalCoordinate d R maxDegree maxRange => classifyByMinimalCubicStableKey (classifyBoundedLocalCoordinate c)) ∧ RatInterval.CaseTable.Sound (externalStableKeyIntervalRowTable rows fallback) (fun c : BoundedLocalCoordinate d R maxDegree maxRange => classifyByMinimalCubicStableKey (classifyBoundedLocalCoordinate c)) value := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.externalStableKeyIntervalRows_covers_and_sound_minimalCubicBoundedLocal_of_keyValue rows fallback value keyValue hcover hvalue hrow


-- created on 2026-10-23
