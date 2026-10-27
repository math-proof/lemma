import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
open Finset Filter Topology StatMech StatMech.Ising


/--
[logZ_dist_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureBCIndep.lean)
-/
@[path]
private lemma logZ_dist_le_eq
  [Fintype Ω]
  [Nonempty Ω]
  {β : ℝ}
  {E₁ E₂ : Ω → ℝ}
  {M : ℝ}
-- given
  (hM : ∀ s, |E₁ s - E₂ s| ≤ M) :
-- imply
  |Real.log (Z β E₁) - Real.log (Z β E₂)| ≤ |β| * M := by
-- proof
  apply StatMech.Ising.logZ_dist_le β E₁ E₂ M hM

/--
[fvZ_eq_Z](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureBCIndep.lean)
-/
@[path]
private lemma fvZ_eq_Z_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (β h : ℝ) :
-- imply
  fvZ η n B β h = Z β (fvEnergy η n B h) := by
-- proof
  apply StatMech.Ising.fvZ_eq_Z η n B β h

/--
[bond_abs_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureBCIndep.lean)
-/
@[path]
private lemma bond_abs_le_one_eq
  {d : ℕ}
  {s : ConfigSpace (Site d)}
  {e : Sym2 (Site d)} :
-- imply
  |bond s e| ≤ 1 := by
-- proof
  apply StatMech.Ising.bond_abs_le_one s e

/--
[fieldSum_indep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureBCIndep.lean)
-/
@[path]
private lemma fieldSum_indep_eq
  {d : ℕ}
  {η₁ η₂ : ConfigSpace (Site d)}
  {n : ℕ}
-- given
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  (∑ x ∈ boxFinset d n, spin (glue η₁ τ) x) = ∑ x ∈ boxFinset d n, spin (glue η₂ τ) x := by
-- proof
  apply StatMech.Ising.fieldSum_indep η₁ η₂ n τ

/--
[bond_internal_indep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureBCIndep.lean)
-/
@[path]
private lemma bond_internal_indep_eq
  {d : ℕ}
  {η₁ η₂ : ConfigSpace (Site d)}
  {n : ℕ}
  {e : Sym2 (Site d)}
-- given
  (τ : {x // x ∈ box d n} → Bool)
  (he : e ∈ bondFinsetInternal d n) :
-- imply
  bond (glue η₁ τ) e = bond (glue η₂ τ) e := by
-- proof
  apply StatMech.Ising.bond_internal_indep η₁ η₂ n τ he

/--
[fvEnergy_sub_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureBCIndep.lean)
-/
@[path]
private lemma fvEnergy_sub_abs_le_eq
  {d : ℕ}
  {η_bc η_free : ConfigSpace (Site d)}
  {n : ℕ}
  {B_bc B_free : Finset (Sym2 (Site d))}
-- given
  (h : ℝ)
  (τ : {x // x ∈ box d n} → Bool)
  (hsub : B_free ⊆ B_bc)
  (hagree : ∀ e ∈ B_free, bond (glue η_bc τ) e = bond (glue η_free τ) e) :
-- imply
  |fvEnergy η_bc n B_bc h τ - fvEnergy η_free n B_free h τ| ≤ (B_bc \ B_free).card := by
-- proof
  apply StatMech.Ising.fvEnergy_sub_abs_le η_bc η_free n B_bc B_free h τ hsub hagree

/--
[logFvZ_sub_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureBCIndep.lean)
-/
@[path]
private lemma logFvZ_sub_abs_le_eq
  {d : ℕ}
  {η_bc η_free : ConfigSpace (Site d)}
  {n : ℕ}
  {B_bc B_free : Finset (Sym2 (Site d))}
-- given
  (β h : ℝ)
  (hsub : B_free ⊆ B_bc)
  (hagree : ∀ (τ : {x // x ∈ box d n} → Bool), ∀ e ∈ B_free, bond (glue η_bc τ) e = bond (glue η_free τ) e) :
-- imply
  |Real.log (fvZ η_bc n B_bc β h) - Real.log (fvZ η_free n B_free β h)| ≤ |β| * (B_bc \ B_free).card := by
-- proof
  apply StatMech.Ising.logFvZ_sub_abs_le η_bc η_free n B_bc B_free β h hsub hagree

/--
[bondFinsetInternal_subset_touch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureBCIndep.lean)
-/
@[path]
private lemma bondFinsetInternal_subset_touch_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  bondFinsetInternal d n ⊆ bondFinsetTouch d n := by
-- proof
  apply StatMech.Ising.bondFinsetInternal_subset_touch n

/--
[internal_bond_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureBCIndep.lean)
-/
@[path]
private lemma internal_bond_agree_eq
  {d : ℕ}
  {n : ℕ}
  {e : Sym2 (Site d)}
-- given
  (τ : {x // x ∈ box d n} → Bool)
  (he : e ∈ bondFinsetInternal d n) :
-- imply
  bond (glue (plusField d) τ) e = bond (glue (minusField d) τ) e := by
-- proof
  apply StatMech.Ising.internal_bond_agree n τ e he

/--
[plus_free_logFvZ_sub_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureBCIndep.lean)
-/
@[path]
private lemma plus_free_logFvZ_sub_abs_le_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (β h : ℝ) :
-- imply
  |Real.log (fvZ (plusField d) n (bondFinsetTouch d n) β h) - Real.log (fvZ (minusField d) n (bondFinsetInternal d n) β h)| ≤ |β| * ((bondFinsetTouch d n) \ (bondFinsetInternal d n)).card := by
-- proof
  apply StatMech.Ising.plus_free_logFvZ_sub_abs_le n β h

/--
[normalized_diff_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureBCIndep.lean)
-/
@[path]
private lemma normalized_diff_tendsto_zero_eq
  {d : ℕ}
  {L₁ L₂ surf vol : ℕ → ℝ}
-- given
  (hbound : ∀ n, |L₁ n - L₂ n| ≤ surf n)
  (hvolpos : ∀ n, 0 < vol n)
  (hratio : Tendsto (fun n => surf n / vol n) atTop (𝓝 0)) :
-- imply
  Tendsto (fun n => L₁ n / vol n - L₂ n / vol n) atTop (𝓝 0) := by
-- proof
  apply StatMech.Ising.normalized_diff_tendsto_zero L₁ L₂ surf vol hbound hvolpos hratio

/--
[boxFinset_card_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureBCIndep.lean)
-/
@[path]
private lemma boxFinset_card_pos_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  0 < ((boxFinset d n).card : ℝ) := by
-- proof
  apply StatMech.Ising.boxFinset_card_pos n

/--
[plus_free_pressure_indep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureBCIndep.lean)
-/
@[path]
private lemma plus_free_pressure_indep_eq
  {d : ℕ}
-- given
  (β h : ℝ)
  (hratio : Tendsto (fun n => (|β| * (((bondFinsetTouch d n) \ (bondFinsetInternal d n)).card : ℝ)) / ((boxFinset d n).card : ℝ)) atTop (𝓝 0)) :
-- imply
  Tendsto (fun n => Real.log (fvZ (plusField d) n (bondFinsetTouch d n) β h) / ((boxFinset d n).card : ℝ) - Real.log (fvZ (minusField d) n (bondFinsetInternal d n) β h) / ((boxFinset d n).card : ℝ)) atTop (𝓝 0) := by
-- proof
  apply StatMech.Ising.plus_free_pressure_indep β h hratio


-- created on 2026-10-23
