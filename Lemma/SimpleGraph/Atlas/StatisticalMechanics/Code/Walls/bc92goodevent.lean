import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc92goodevent
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc92_count_on_good_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc92goodevent.lean)
-/
@[path]
private lemma bc92_count_on_good_event_eq
  {d : ℕ}
  {L R : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hω : ω ∈ bc92_GoodEvent (d := d) L R) :
-- imply
  bc73_SublatticeForest ω L R := by
-- proof
  apply StatMech.Walls.bc92_count_on_good_event L R hω

/--
[bc92_coarseTcount_le_on_good_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc92goodevent.lean)
-/
@[path]
private lemma bc92_coarseTcount_le_on_good_event_eq
  {d : ℕ}
  {L R : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hω : ω ∈ bc92_GoodEvent (d := d) L R) :
-- imply
  bc61_coarseTcount ω L R ≤ (2 * L + 1) ^ d * boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc92_coarseTcount_le_on_good_event L R hω

/--
[bc92_good_event_of_gnData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc92goodevent.lean)
-/
@[path]
private lemma bc92_good_event_of_gnData_eq
  {d : ℕ}
  {L R : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : ∀ c : Fin d → Fin (2 * L + 1), bc75_FiberGnTrifData ω L R c) :
-- imply
  ω ∈ bc92_GoodEvent (d := d) L R := by
-- proof
  apply StatMech.Walls.bc92_good_event_of_gnData L R h

/--
[bc92_good_event_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc92goodevent.lean)
-/
@[path]
private lemma bc92_good_event_of_noTrif_eq
  {d : ℕ}
  {L R : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hno : bc61_coarseTrifFinset ω L R = ∅) :
-- imply
  ω ∈ bc92_GoodEvent (d := d) L R := by
-- proof
  apply StatMech.Walls.bc92_good_event_of_noTrif L R hno

/--
[bc92_measurableSet_coarseTrifFinset_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc92goodevent.lean)
-/
@[path]
private lemma bc92_measurableSet_coarseTrifFinset_eq_eq
  {d : ℕ}
  {L R : ℕ}
  {T : Finset (Site d)} :
-- imply
  MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | bc61_coarseTrifFinset ω L R = T} := by
-- proof
  apply StatMech.Walls.bc92_measurableSet_coarseTrifFinset_eq L R T

/--
[bc92_measurableSet_goodEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc92goodevent.lean)
-/
@[path]
private lemma bc92_measurableSet_goodEvent_eq
  {d : ℕ}
  {L R : ℕ} :
-- imply
  MeasurableSet (bc92_GoodEvent (d := d) L R) := by
-- proof
  apply StatMech.Walls.bc92_measurableSet_goodEvent L R

/--
[bc92_good_event_ae_iff_forest_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc92goodevent.lean)
-/
@[path]
private lemma bc92_good_event_ae_iff_forest_ae_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ} :
-- imply
  (∀ R : ℕ, μ (bc92_GoodEvent (d := d) L R) = 1) ↔ (∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) := by
-- proof
  apply StatMech.Walls.bc92_good_event_ae_iff_forest_ae μ L

/--
[bc92_ae_count_of_good_event_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc92goodevent.lean)
-/
@[path]
private lemma bc92_ae_count_of_good_event_ae_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hgood : ∀ R : ℕ, μ (bc92_GoodEvent (d := d) L R) = 1)
  (hexist : bc61_CoarseTrifExistence μ L) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc92_ae_count_of_good_event_ae μ hd L hinv hgood hexist

/--
[bc92_good_event_ae_of_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc92goodevent.lean)
-/
@[path]
private lemma bc92_good_event_ae_of_dichotomy_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (h0 : μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) :
-- imply
  ∀ R : ℕ, μ (bc92_GoodEvent (d := d) L R) = 1 := by
-- proof
  apply StatMech.Walls.bc92_good_event_ae_of_dichotomy μ L hinv h0

/--
[bc92_good_event_ae_from_finiteEnergy_is_circular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc92goodevent.lean)
-/
@[path]
private lemma bc92_good_event_ae_from_finiteEnergy_is_circular_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hexist : bc61_CoarseTrifExistence μ L) :
-- imply
  ((∀ R : ℕ, μ (bc92_GoodEvent (d := d) L R) = 1) → μ {ω | numInfiniteClusters d ω = ⊤} = 0) ∧ ((μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) → ∀ R : ℕ, μ (bc92_GoodEvent (d := d) L R) = 1) := by
-- proof
  apply StatMech.Walls.bc92_good_event_ae_from_finiteEnergy_is_circular μ hd L hinv hexist

/--
[bc92_upperLines_N_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc92goodevent.lean)
-/
@[path]
private lemma bc92_upperLines_N_top_eq
  {d : ℕ} :
-- imply
  numInfiniteClusters 2 bc60_upperLines = ⊤ := by
-- proof
  apply StatMech.Walls.bc92_upperLines_N_top

/--
[bc92_upperLines_null_of_goal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc92goodevent.lean)
-/
@[path]
private lemma bc92_upperLines_null_of_goal_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
-- given
  (htop : μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) :
-- imply
  μ {ω : ConfigSpace (Sym2 (Site 2)) | ω = bc60_upperLines} = 0 := by
-- proof
  apply StatMech.Walls.bc92_upperLines_null_of_goal μ htop

/--
[bc92_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc92goodevent.lean)
-/
@[path]
private lemma bc92_status_eq
  {d : ℕ} :
-- imply
  (∀ (L R : ℕ) (ω : ConfigSpace (Sym2 (Site 2))), ω ∈ bc92_GoodEvent (d := 2) L R → bc61_coarseTcount ω L R ≤ (2 * L + 1) ^ 2 * boxSV_boundaryCard 2 R) ∧ (∀ (L R : ℕ) (ω : ConfigSpace (Sym2 (Site 2))), bc61_coarseTrifFinset ω L R = ∅ → ω ∈ bc92_GoodEvent (d := 2) L R) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ), IsTranslationInvariant (G := Multiplicative (Site 2)) μ → (∀ R : ℕ, μ (bc92_GoodEvent (d := 2) L R) = 1) → bc61_CoarseTrifExistence μ L → μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ), (∀ R : ℕ, μ (bc92_GoodEvent (d := 2) L R) = 1) ↔ (∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R)) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ), IsTranslationInvariant (G := Multiplicative (Site 2)) μ → μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 → ∀ R : ℕ, μ (bc92_GoodEvent (d := 2) L R) = 1) ∧ (numInfiniteClusters 2 bc60_upperLines = ⊤) := by
-- proof
  apply StatMech.Walls.bc92_status


-- created on 2026-10-23
