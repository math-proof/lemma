import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose.Part2
open MeasureTheory Measure Set MeasurableSpace ProbabilityTheory Filter Finset StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[bkc_infinitePi_disjoint_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose.lean)
-/
@[path]
private lemma bkc_infinitePi_disjoint_cylinder_eq
  {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)]
  {μ : (i : ι) → Measure (X i)}
  [∀ i, IsProbabilityMeasure (μ i)]
  {s t : Finset ι}
  {S : Set (Π i : s, X i)}
  {T : Set (Π i : t, X i)}
-- given
  (hS : MeasurableSet S)
  (hT : MeasurableSet T)
  (hd : Disjoint s t) :
-- imply
  Measure.infinitePi μ (cylinder s S ∩ cylinder t T) = Measure.infinitePi μ (cylinder s S) * Measure.infinitePi μ (cylinder t T) := by
-- proof
  apply StatMech.Percolation.bkc_infinitePi_disjoint_cylinder μ hS hT hd

/--
[bkc_projP_preimage_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose.lean)
-/
@[path]
private lemma bkc_projP_preimage_cylinder_eq
  {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)]
  {s : Finset (Subtype p)}
  {S : Set (Π j : s, X ((j : Subtype p) : ι))}
-- given
  (p : ι → Prop) :
-- imply
  (fun (ω : Π i, X i) (j' : Subtype p) => ω (j' : ι)) ⁻¹' (cylinder s S) = cylinder (s.map (Function.Embedding.subtype p)) ((fun (y : Π i : s.map (Function.Embedding.subtype p), X (i : ι)) (j : s) => y ⟨((j : Subtype p) : ι), by rw [Finset.mem_map]; exact ⟨(j : Subtype p), j.2, rfl⟩⟩) ⁻¹' S) := by
-- proof
  apply StatMech.Percolation.bkc_projP_preimage_cylinder p s S

/--
[bkc_infinitePi_map_piEquivPiSubtypeProd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose.lean)
-/
@[path]
private lemma bkc_infinitePi_map_piEquivPiSubtypeProd_eq
  {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)]
  {μ : (i : ι) → Measure (X i)}
  [∀ i, IsProbabilityMeasure (μ i)]
  [DecidablePred p]
-- given
  (p : ι → Prop) :
-- imply
  (Measure.infinitePi μ).map (MeasurableEquiv.piEquivPiSubtypeProd X p) = (Measure.infinitePi (fun j : Subtype p => μ (j : ι))).prod (Measure.infinitePi (fun j : {i // ¬ p i} => μ (j : ι))) := by
-- proof
  apply StatMech.Percolation.bkc_infinitePi_map_piEquivPiSubtypeProd μ p

/--
[bkc_pi_absolutelyContinuous_fin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose.lean)
-/
@[path]
private lemma bkc_pi_absolutelyContinuous_fin_eq
  {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)] :
-- imply
  ∀ (n : ℕ) {Y : Fin n → Type*} [∀ k, MeasurableSpace (Y k)] (ν μ : (k : Fin n) → Measure (Y k)) [∀ k, IsProbabilityMeasure (μ k)] [∀ k, IsProbabilityMeasure (ν k)], (∀ k, ν k ≪ μ k) → Measure.pi ν ≪ Measure.pi μ := by
-- proof
  apply StatMech.Percolation.bkc_pi_absolutelyContinuous_fin

/--
[bkc_pi_absolutelyContinuous_fintype](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose.lean)
-/
@[path]
private lemma bkc_pi_absolutelyContinuous_fintype_eq
  {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)]
  [Fintype κ]
  {Y : κ → Type*}
  [∀ k, MeasurableSpace (Y k)]
  {ν μ : (k : κ) → Measure (Y k)}
  [∀ k, IsProbabilityMeasure (μ k)]
  [∀ k, IsProbabilityMeasure (ν k)]
-- given
  (h : ∀ k, ν k ≪ μ k) :
-- imply
  Measure.pi ν ≪ Measure.pi μ := by
-- proof
  apply StatMech.Percolation.bkc_pi_absolutelyContinuous_fintype ν μ h

/--
[bkc_infinitePi_ac_of_finite_diff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose.lean)
-/
@[path]
private lemma bkc_infinitePi_ac_of_finite_diff_eq
  {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)]
  {ν μ : (i : ι) → Measure (X i)}
  [∀ i, IsProbabilityMeasure (μ i)]
  [∀ i, IsProbabilityMeasure (ν i)]
  {F : Finset ι}
-- given
  (hdiff : ∀ i ∉ F, ν i = μ i)
  (hac : ∀ i, ν i ≪ μ i) :
-- imply
  Measure.infinitePi ν ≪ Measure.infinitePi μ := by
-- proof
  apply StatMech.Percolation.bkc_infinitePi_ac_of_finite_diff ν μ F hdiff hac

/--
[bkc_factor_ac](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose.lean)
-/
@[path]
private lemma bkc_factor_ac_eq
  {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)]
  {d : ℕ}
  {e : Sym2 (Site d)}
  {F : Finset (Sym2 (Site d))}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hp0 : 0 < p) :
-- imply
  (bernoulliMeasure p hp).map (fun b => if e ∈ F then true else b) ≪ bernoulliMeasure p hp := by
-- proof
  apply StatMech.Percolation.bkc_factor_ac p hp hp0 e F

/--
[bkc_bernoulli_hasFiniteEnergyMerge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose.lean)
-/
@[path]
private lemma bkc_bernoulli_hasFiniteEnergyMerge_eq
  {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)]
  {d : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hp0 : 0 < p) :
-- imply
  HasFiniteEnergyMerge (d := d) (bernoulliProductMeasure (E := Sym2 (Site d)) p hp) := by
-- proof
  apply StatMech.Percolation.bkc_bernoulli_hasFiniteEnergyMerge p hp hp0

/--
[bkc_smul_site_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose.lean)
-/
@[path]
private lemma bkc_smul_site_injective_eq
  {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)]
  {d : ℕ}
  {a : Site d} :
-- imply
  Function.Injective (fun g : Multiplicative (Site d) => g • a) := by
-- proof
  apply StatMech.Percolation.bkc_smul_site_injective a

/--
[bkc_smul_sym2_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose.lean)
-/
@[path]
private lemma bkc_smul_sym2_injective_eq
  {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)]
  {d : ℕ}
  {a : Sym2 (Site d)} :
-- imply
  Function.Injective (fun g : Multiplicative (Site d) => g • a) := by
-- proof
  apply StatMech.Percolation.bkc_smul_sym2_injective a

/--
[bkc_bernoulli_isErgodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose.lean)
-/
@[path]
private lemma bkc_bernoulli_isErgodic_eq
  {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)]
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (bernoulliProductMeasure (E := Sym2 (Site d)) p hp) := by
-- proof
  apply StatMech.Percolation.bkc_bernoulli_isErgodic hd p hp

/--
[bkc_boxFinsetBK_card_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose.lean)
-/
@[path]
private lemma bkc_boxFinsetBK_card_pos_eq
  {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)]
  {d : ℕ}
  {d n : ℕ} :
-- imply
  0 < (boxFinsetBK d n).card := by
-- proof
  apply StatMech.Percolation.bkc_boxFinsetBK_card_pos d n

/--
[bkc_boundary_vol_ratio_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose.lean)
-/
@[path]
private lemma bkc_boundary_vol_ratio_le_eq
  {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)]
  {d : ℕ}
  {d n : ℕ}
-- given
  (hd : 1 ≤ d)
  (hn : 1 ≤ n) :
-- imply
  (boxSV_boundaryCard d n : ℝ) / ((boxFinsetBK d n).card : ℝ) ≤ (2 * d : ℝ) / n := by
-- proof
  apply StatMech.Percolation.bkc_boundary_vol_ratio_le d n hd hn

/--
[bkc_boundary_vol_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose.lean)
-/
@[path]
private lemma bkc_boundary_vol_tendsto_eq
  {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)]
  {d : ℕ}
  {d : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  Tendsto (fun n => (boxSV_boundaryCard d n : ℝ) / ((boxFinsetBK d n).card : ℝ)) atTop (𝓝 0) := by
-- proof
  apply StatMech.Percolation.bkc_boundary_vol_tendsto d hd

/--
[bkc_burton_keane_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose.lean)
-/
@[path]
private lemma bkc_burton_keane_bernoulli_eq
  {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)]
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ boxSV_boundaryCard d n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.bkc_burton_keane_bernoulli hd p hp1 hp0 hbound htrif


-- created on 2026-10-23
