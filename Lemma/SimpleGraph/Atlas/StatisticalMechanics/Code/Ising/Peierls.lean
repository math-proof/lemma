import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.Peierls
open MeasureTheory Filter Topology Finset StatMech StatMech.Ising


/--
[flipConfig_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean)
-/
@[path]
private lemma flipConfig_apply_eq
  {d : ℕ}
  {s : ConfigSpace (Site d)}
  {y : Site d} :
-- imply
  flipConfig s y = !(s y) := by
-- proof
  apply StatMech.Ising.flipConfig_apply s y

/--
[flipConfig_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean)
-/
@[path]
private lemma flipConfig_involutive_eq
  {d : ℕ}
  {s : ConfigSpace (Site d)} :
-- imply
  flipConfig (flipConfig s) = s := by
-- proof
  apply StatMech.Ising.flipConfig_involutive s

/--
[flipInterior_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean)
-/
@[path]
private lemma flipInterior_involutive_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  flipInterior (flipInterior τ) = τ := by
-- proof
  apply StatMech.Ising.flipInterior_involutive τ

/--
[flipInteriorEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean)
-/
@[path]
private lemma flipInteriorEquiv_apply_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  flipInteriorEquiv τ = flipInterior τ := by
-- proof
  apply StatMech.Ising.flipInteriorEquiv_apply τ

/--
[flipConfig_plusField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean)
-/
@[path]
private lemma flipConfig_plusField_eq
  {d : ℕ} :
-- imply
  flipConfig (plusField d) = minusField d := by
-- proof
  apply StatMech.Ising.flipConfig_plusField

/--
[flipConfig_minusField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean)
-/
@[path]
private lemma flipConfig_minusField_eq
  {d : ℕ} :
-- imply
  flipConfig (minusField d) = plusField d := by
-- proof
  apply StatMech.Ising.flipConfig_minusField

/--
[spin_flipConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean)
-/
@[path]
private lemma spin_flipConfig_eq
  {d : ℕ}
  {s : ConfigSpace (Site d)}
  {x : Site d} :
-- imply
  spin (flipConfig s) x = - spin s x := by
-- proof
  apply StatMech.Ising.spin_flipConfig s x

/--
[bond_flipConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean)
-/
@[path]
private lemma bond_flipConfig_eq
  {d : ℕ}
  {s : ConfigSpace (Site d)}
  {e : Sym2 (Site d)} :
-- imply
  bond (flipConfig s) e = bond s e := by
-- proof
  apply StatMech.Ising.bond_flipConfig s e

/--
[glue_flipConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean)
-/
@[path]
private lemma glue_flipConfig_eq
  {d : ℕ}
  {n : ℕ}
  {η : ConfigSpace (Site d)}
-- given
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  flipConfig (glue η τ) = glue (flipConfig η) (flipInterior τ) := by
-- proof
  apply StatMech.Ising.glue_flipConfig η τ

/--
[fvEnergy_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean)
-/
@[path]
private lemma fvEnergy_flip_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (h : ℝ)
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  fvEnergy (flipConfig η) n B (-h) (flipInterior τ) = fvEnergy η n B h τ := by
-- proof
  apply StatMech.Ising.fvEnergy_flip η n B h τ

/--
[fvWeight_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean)
-/
@[path]
private lemma fvWeight_flip_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (β h : ℝ)
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  fvWeight (flipConfig η) n B β (-h) (flipInterior τ) = fvWeight η n B β h τ := by
-- proof
  apply StatMech.Ising.fvWeight_flip η n B β h τ

/--
[fvZ_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean)
-/
@[path]
private lemma fvZ_flip_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (β h : ℝ) :
-- imply
  fvZ (flipConfig η) n B β (-h) = fvZ η n B β h := by
-- proof
  apply StatMech.Ising.fvZ_flip η n B β h

/--
[fvProb_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean)
-/
@[path]
private lemma fvProb_flip_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (β h : ℝ)
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  fvProb (flipConfig η) n B β (-h) (flipInterior τ) = fvProb η n B β h τ := by
-- proof
  apply StatMech.Ising.fvProb_flip η n B β h τ

/--
[measurable_flipConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean)
-/
@[path]
private lemma measurable_flipConfig_eq
  {d : ℕ} :
-- imply
  Measurable (flipConfig : ConfigSpace (Site d) → ConfigSpace (Site d)) := by
-- proof
  apply StatMech.Ising.measurable_flipConfig

/--
[continuous_flipConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean)
-/
@[path]
private lemma continuous_flipConfig_eq
  {d : ℕ} :
-- imply
  Continuous (flipConfig : ConfigSpace (Site d) → ConfigSpace (Site d)) := by
-- proof
  apply StatMech.Ising.continuous_flipConfig

/--
[map_finsetSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean)
-/
@[path]
private lemma map_finsetSum_eq
  {d : ℕ}
  [MeasurableSpace α]
  {f : α → α}
  {s : Finset ι}
  {μ : ι → Measure α}
-- given
  (hf : Measurable f) :
-- imply
  Measure.map f (∑ i ∈ s, μ i) = ∑ i ∈ s, Measure.map f (μ i) := by
-- proof
  apply StatMech.Ising.map_finsetSum hf s μ

/--
[map_fvMeasure_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean)
-/
@[path]
private lemma map_fvMeasure_flip_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (β h : ℝ) :
-- imply
  Measure.map flipConfig (fvMeasure η n B β h) = fvMeasure (flipConfig η) n B β (-h) := by
-- proof
  apply StatMech.Ising.map_fvMeasure_flip η n B β h

/--
[map_minusMeasure_eq_plusMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean)
-/
@[path]
private lemma map_minusMeasure_eq_plusMeasure_eq
  {d : ℕ}
  {n : ℕ}
  {β : ℝ} :
-- imply
  Measure.map flipConfig ((minusMeasure d n β 0 : ProbabilityMeasure (ConfigSpace (Site d))) : Measure (ConfigSpace (Site d))) = ((plusMeasure d n β 0 : ProbabilityMeasure (ConfigSpace (Site d))) : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.map_minusMeasure_eq_plusMeasure n β

/--
[origin_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean)
-/
@[path]
private lemma origin_mem_box_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  origin d ∈ box d n := by
-- proof
  apply StatMech.Ising.origin_mem_box n

/--
[continuous_spin_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean)
-/
@[path]
private lemma continuous_spin_apply_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  Continuous (fun s : ConfigSpace (Site d) => spin s x) := by
-- proof
  apply StatMech.Ising.continuous_spin_apply x

/--
[fvMagOrigin_eq_integral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean)
-/
@[path]
private lemma fvMagOrigin_eq_integral_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (β h : ℝ) :
-- imply
  fvMagOrigin η n B β h = ∫ s, spin s (origin d) ∂(fvMeasure η n B β h) := by
-- proof
  apply StatMech.Ising.fvMagOrigin_eq_integral η n B β h

/--
[fvMagOrigin_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean)
-/
@[path]
private lemma fvMagOrigin_flip_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (β h : ℝ) :
-- imply
  fvMagOrigin (flipConfig η) n B β (-h) = - fvMagOrigin η n B β h := by
-- proof
  apply StatMech.Ising.fvMagOrigin_flip η n B β h

/--
[fvMagOrigin_minus_eq_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean)
-/
@[path]
private lemma fvMagOrigin_minus_eq_neg_eq
  {d : ℕ}
  {n : ℕ}
  {β : ℝ} :
-- imply
  fvMagOrigin (minusField d) n (bondFinsetTouch d n) β 0 = - fvMagOrigin (plusField d) n (bondFinsetTouch d n) β 0 := by
-- proof
  apply StatMech.Ising.fvMagOrigin_minus_eq_neg n β

/--
[fvMagOrigin_plus_eq_integral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean)
-/
@[path]
private lemma fvMagOrigin_plus_eq_integral_eq
  {d : ℕ}
  {n : ℕ}
  {β : ℝ} :
-- imply
  fvMagOrigin (plusField d) n (bondFinsetTouch d n) β 0 = ∫ s, spin s (origin d) ∂((plusMeasure d n β 0 : ProbabilityMeasure (ConfigSpace (Site d))) : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.fvMagOrigin_plus_eq_integral n β

/--
[fvMagOrigin_minus_eq_integral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean)
-/
@[path]
private lemma fvMagOrigin_minus_eq_integral_eq
  {d : ℕ}
  {n : ℕ}
  {β : ℝ} :
-- imply
  fvMagOrigin (minusField d) n (bondFinsetTouch d n) β 0 = ∫ s, spin s (origin d) ∂((minusMeasure d n β 0 : ProbabilityMeasure (ConfigSpace (Site d))) : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.fvMagOrigin_minus_eq_integral n β

/--
[plusMeasure_ne_minusMeasure_of_fvMagOrigin_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean)
-/
@[path]
private lemma plusMeasure_ne_minusMeasure_of_fvMagOrigin_ne_zero_eq
  {d : ℕ}
  {n : ℕ}
  {β : ℝ}
-- given
  (hm : fvMagOrigin (plusField d) n (bondFinsetTouch d n) β 0 ≠ 0) :
-- imply
  plusMeasure d n β 0 ≠ minusMeasure d n β 0 := by
-- proof
  apply StatMech.Ising.plusMeasure_ne_minusMeasure_of_fvMagOrigin_ne_zero n β hm

/--
[peierls_lro_criterion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean)
-/
@[path]
private lemma peierls_lro_criterion_eq
  {d : ℕ}
  {n : ℕ}
  {β : ℝ}
-- given
  (hd : 2 ≤ d)
  (hPeierls : 0 < fvMagOrigin (plusField d) n (bondFinsetTouch d n) β 0) :
-- imply
  plusMeasure d n β 0 ≠ minusMeasure d n β 0 := by
-- proof
  apply StatMech.Ising.peierls_lro_criterion hd n β hPeierls


-- created on 2026-10-23
