import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology StatMech StatMech.Ising


/--
[resBox_ovrBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FVConsistencyProve.lean)
-/
@[path]
private lemma resBox_ovrBox_eq
  {d : ℕ}
  {n m : ℕ}
-- given
  (hnm : n ≤ m)
  (σ : {x // x ∈ box d m} → Bool)
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  resBox hnm (ovrBox hnm σ τ) = τ := by
-- proof
  apply StatMech.Ising.resBox_ovrBox hnm σ τ

/--
[ovrBox_ovrBox_resBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FVConsistencyProve.lean)
-/
@[path]
private lemma ovrBox_ovrBox_resBox_eq
  {d : ℕ}
  {n m : ℕ}
-- given
  (hnm : n ≤ m)
  (σ : {x // x ∈ box d m} → Bool)
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  ovrBox hnm (ovrBox hnm σ τ) (resBox hnm σ) = σ := by
-- proof
  apply StatMech.Ising.ovrBox_ovrBox_resBox hnm σ τ

/--
[glue_glue_eq_glue_ovrBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FVConsistencyProve.lean)
-/
@[path]
private lemma glue_glue_eq_glue_ovrBox_eq
  {d : ℕ}
  {n m : ℕ}
  {η : ConfigSpace (Site d)}
-- given
  (hnm : n ≤ m)
  (σ : {x // x ∈ box d m} → Bool)
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  glue (glue η σ) τ = glue η (ovrBox hnm σ τ) := by
-- proof
  apply StatMech.Ising.glue_glue_eq_glue_ovrBox hnm η σ τ

/--
[glue_ovrBox_eq_off_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FVConsistencyProve.lean)
-/
@[path]
private lemma glue_ovrBox_eq_off_box_eq
  {d : ℕ}
  {n m : ℕ}
  {η : ConfigSpace (Site d)}
  {x : Site d}
-- given
  (hnm : n ≤ m)
  (σ : {x // x ∈ box d m} → Bool)
  (τ : {x // x ∈ box d n} → Bool)
  (hx : x ∉ box d n) :
-- imply
  glue η (ovrBox hnm σ τ) x = glue η σ x := by
-- proof
  apply StatMech.Ising.glue_ovrBox_eq_off_box hnm η σ τ hx

/--
[bond_glue_ovrBox_eq_of_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FVConsistencyProve.lean)
-/
@[path]
private lemma bond_glue_ovrBox_eq_of_notMem_eq
  {d : ℕ}
  {n m : ℕ}
  {η : ConfigSpace (Site d)}
  {e : Sym2 (Site d)}
-- given
  (hnm : n ≤ m)
  (σ : {x // x ∈ box d m} → Bool)
  (τ : {x // x ∈ box d n} → Bool)
  (heE : e ∈ (hypercubicLattice d).edgeSet)
  (heB : e ∉ bondFinsetTouch d n) :
-- imply
  bond (glue η (ovrBox hnm σ τ)) e = bond (glue η σ) e := by
-- proof
  apply StatMech.Ising.bond_glue_ovrBox_eq_of_notMem hnm η σ τ heE heB

/--
[bondFinsetTouch_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FVConsistencyProve.lean)
-/
@[path]
private lemma bondFinsetTouch_subset_eq
  {d : ℕ}
  {n m : ℕ}
-- given
  (hnm : n ≤ m) :
-- imply
  bondFinsetTouch d n ⊆ bondFinsetTouch d m := by
-- proof
  apply StatMech.Ising.bondFinsetTouch_subset hnm

/--
[bond_sum_diff_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FVConsistencyProve.lean)
-/
@[path]
private lemma bond_sum_diff_eq_eq
  {d : ℕ}
  {n m : ℕ}
  {η : ConfigSpace (Site d)}
-- given
  (hnm : n ≤ m)
  (σ : {x // x ∈ box d m} → Bool)
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  (∑ e ∈ bondFinsetTouch d m, bond (glue η (ovrBox hnm σ τ)) e) - (∑ e ∈ bondFinsetTouch d m, bond (glue η σ) e) = (∑ e ∈ bondFinsetTouch d n, bond (glue η (ovrBox hnm σ τ)) e) - (∑ e ∈ bondFinsetTouch d n, bond (glue η σ) e) := by
-- proof
  apply StatMech.Ising.bond_sum_diff_eq hnm η σ τ

/--
[spin_sum_diff_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FVConsistencyProve.lean)
-/
@[path]
private lemma spin_sum_diff_eq_eq
  {d : ℕ}
  {n m : ℕ}
  {η : ConfigSpace (Site d)}
-- given
  (hnm : n ≤ m)
  (σ : {x // x ∈ box d m} → Bool)
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  (∑ x ∈ boxFinset d m, spin (glue η (ovrBox hnm σ τ)) x) - (∑ x ∈ boxFinset d m, spin (glue η σ) x) = (∑ x ∈ boxFinset d n, spin (glue η (ovrBox hnm σ τ)) x) - (∑ x ∈ boxFinset d n, spin (glue η σ) x) := by
-- proof
  apply StatMech.Ising.spin_sum_diff_eq hnm η σ τ

/--
[fv_energy_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FVConsistencyProve.lean)
-/
@[path]
private lemma fv_energy_decomp_eq
  {d : ℕ}
  {n m : ℕ}
  {η : ConfigSpace (Site d)}
-- given
  (hnm : n ≤ m)
  (h : ℝ)
  (σ : {x // x ∈ box d m} → Bool)
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  fvEnergy η m (bondFinsetTouch d m) h σ + fvEnergy (glue η σ) n (bondFinsetTouch d n) h τ = fvEnergy η m (bondFinsetTouch d m) h (ovrBox hnm σ τ) + fvEnergy (glue η (ovrBox hnm σ τ)) n (bondFinsetTouch d n) h (resBox hnm σ) := by
-- proof
  apply StatMech.Ising.fv_energy_decomp hnm η h σ τ

/--
[fvWeight_spec_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FVConsistencyProve.lean)
-/
@[path]
private lemma fvWeight_spec_symm_eq
  {d : ℕ}
  {n m : ℕ}
  {η : ConfigSpace (Site d)}
-- given
  (hnm : n ≤ m)
  (β h : ℝ)
  (σ : {x // x ∈ box d m} → Bool)
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  fvWeight η m (bondFinsetTouch d m) β h σ * fvWeight (glue η σ) n (bondFinsetTouch d n) β h τ = fvWeight η m (bondFinsetTouch d m) β h (ovrBox hnm σ τ) * fvWeight (glue η (ovrBox hnm σ τ)) n (bondFinsetTouch d n) β h (resBox hnm σ) := by
-- proof
  apply StatMech.Ising.fvWeight_spec_symm hnm η β h σ τ

/--
[integral_fvMeasure_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FVConsistencyProve.lean)
-/
@[path]
private lemma integral_fvMeasure_eq_sum_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {g : ConfigSpace (Site d) → ℝ}
-- given
  (β h : ℝ) :
-- imply
  ∫ y, g y ∂(fvMeasure η n B β h) = ∑ τ : {x // x ∈ box d n} → Bool, fvProb η n B β h τ * g (glue η τ) := by
-- proof
  apply StatMech.Ising.integral_fvMeasure_eq_sum η n B β h g

/--
[plusMeasure_coe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FVConsistencyProve.lean)
-/
@[path]
private lemma plusMeasure_coe_eq
  {d : ℕ}
  {m : ℕ}
-- given
  (β h : ℝ) :
-- imply
  (plusMeasure d m β h : Measure (ConfigSpace (Site d))) = fvMeasure (plusField d) m (bondFinsetTouch d m) β h := by
-- proof
  apply StatMech.Ising.plusMeasure_coe m β h

/--
[glue_eq_of_agree_off_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FVConsistencyProve.lean)
-/
@[path]
private lemma glue_eq_of_agree_off_box_eq
  {d : ℕ}
  {n : ℕ}
  {ζ₁ ζ₂ : ConfigSpace (Site d)}
-- given
  (hagree : ∀ x ∉ box d n, ζ₁ x = ζ₂ x)
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  glue ζ₁ τ = glue ζ₂ τ := by
-- proof
  apply StatMech.Ising.glue_eq_of_agree_off_box hagree τ

/--
[fvWeight_eq_of_agree_off_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FVConsistencyProve.lean)
-/
@[path]
private lemma fvWeight_eq_of_agree_off_box_eq
  {d : ℕ}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {ζ₁ ζ₂ : ConfigSpace (Site d)}
-- given
  (β h : ℝ)
  (hagree : ∀ x ∉ box d n, ζ₁ x = ζ₂ x)
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  fvWeight ζ₁ n B β h τ = fvWeight ζ₂ n B β h τ := by
-- proof
  apply StatMech.Ising.fvWeight_eq_of_agree_off_box B β h hagree τ

/--
[fvZ_eq_of_agree_off_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FVConsistencyProve.lean)
-/
@[path]
private lemma fvZ_eq_of_agree_off_box_eq
  {d : ℕ}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {ζ₁ ζ₂ : ConfigSpace (Site d)}
-- given
  (β h : ℝ)
  (hagree : ∀ x ∉ box d n, ζ₁ x = ζ₂ x) :
-- imply
  fvZ ζ₁ n B β h = fvZ ζ₂ n B β h := by
-- proof
  apply StatMech.Ising.fvZ_eq_of_agree_off_box B β h hagree

/--
[fvProb_eq_of_agree_off_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FVConsistencyProve.lean)
-/
@[path]
private lemma fvProb_eq_of_agree_off_box_eq
  {d : ℕ}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {ζ₁ ζ₂ : ConfigSpace (Site d)}
-- given
  (β h : ℝ)
  (hagree : ∀ x ∉ box d n, ζ₁ x = ζ₂ x)
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  fvProb ζ₁ n B β h τ = fvProb ζ₂ n B β h τ := by
-- proof
  apply StatMech.Ising.fvProb_eq_of_agree_off_box B β h hagree τ

/--
[swapPair_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FVConsistencyProve.lean)
-/
@[path]
private lemma swapPair_involutive_eq
  {d : ℕ}
  {n m : ℕ}
-- given
  (hnm : n ≤ m) :
-- imply
  Function.Involutive (swapPair (d := d) hnm) := by
-- proof
  apply StatMech.Ising.swapPair_involutive hnm

/--
[swapPair_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FVConsistencyProve.lean)
-/
@[path]
private lemma swapPair_bijective_eq
  {d : ℕ}
  {n m : ℕ}
-- given
  (hnm : n ≤ m) :
-- imply
  Function.Bijective (swapPair (d := d) hnm) := by
-- proof
  apply StatMech.Ising.swapPair_bijective hnm

/--
[consistency_double_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FVConsistencyProve.lean)
-/
@[path]
private lemma consistency_double_sum_eq
  {d : ℕ}
  {n m : ℕ}
  {η : ConfigSpace (Site d)}
  {g : ConfigSpace (Site d) → ℝ}
-- given
  (hnm : n ≤ m)
  (β h : ℝ) :
-- imply
  (∑ σ : {x // x ∈ box d m} → Bool, fvProb η m (bondFinsetTouch d m) β h σ * ∑ τ : {x // x ∈ box d n} → Bool, fvProb (glue η σ) n (bondFinsetTouch d n) β h τ * g (glue (glue η σ) τ)) = ∑ σ : {x // x ∈ box d m} → Bool, fvProb η m (bondFinsetTouch d m) β h σ * g (glue η σ) := by
-- proof
  apply StatMech.Ising.consistency_double_sum hnm η β h g

/--
[fvConsistency_plus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FVConsistencyProve.lean)
-/
@[path]
private lemma fvConsistency_plus_eq
  {d : ℕ}
-- given
  (β h : ℝ) :
-- imply
  FVConsistency d β h := by
-- proof
  apply StatMech.Ising.fvConsistency_plus β h

/--
[psdlr_plusState_isDLR_uncond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FVConsistencyProve.lean)
-/
@[path]
private lemma psdlr_plusState_isDLR_uncond_eq
  {d : ℕ}
-- given
  (β h : ℝ) :
-- imply
  IsDLRState d β h (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.psdlr_plusState_isDLR_uncond β h


-- created on 2026-10-23
