import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction StatMech StatMech.Ising


/--
[gv_self_mem_ball](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gv_self_mem_ball_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  x ∈ gvBall x := by
-- proof
  apply StatMech.Ising.gv_self_mem_ball x

/--
[gv_nbr_mem_ball](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gv_nbr_mem_ball_eq
  {d : ℕ}
  {x y : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj x y) :
-- imply
  y ∈ gvBall x := by
-- proof
  apply StatMech.Ising.gv_nbr_mem_ball hadj

/--
[gv_mk_mem_bondTouch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gv_mk_mem_bondTouch_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {x y : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj x y)
  (htouch : x ∈ S ∨ y ∈ S) :
-- imply
  s(x, y) ∈ gvBondTouch S := by
-- proof
  apply StatMech.Ising.gv_mk_mem_bondTouch hadj htouch

/--
[gv_bondTouch_subset_edgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gv_bondTouch_subset_edgeSet_eq
  {d : ℕ}
  {S : Finset (Site d)} :
-- imply
  ∀ e ∈ gvBondTouch S, e ∈ (hypercubicLattice d).edgeSet := by
-- proof
  apply StatMech.Ising.gv_bondTouch_subset_edgeSet S

/--
[gv_bondTouch_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gv_bondTouch_subset_eq
  {d : ℕ}
  {Sin Sout : Finset (Site d)}
-- given
  (hsub : Sin ⊆ Sout) :
-- imply
  gvBondTouch Sin ⊆ gvBondTouch Sout := by
-- proof
  apply StatMech.Ising.gv_bondTouch_subset hsub

/--
[gvGlue_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gvGlue_mem_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {S : Finset (Site d)}
  {x : Site d}
-- given
  (τ : {x // x ∈ S} → Bool)
  (hx : x ∈ S) :
-- imply
  gvGlue η S τ x = τ ⟨x, hx⟩ := by
-- proof
  apply StatMech.Ising.gvGlue_mem η S τ hx

/--
[gvGlue_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gvGlue_not_mem_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {S : Finset (Site d)}
  {x : Site d}
-- given
  (τ : {x // x ∈ S} → Bool)
  (hx : x ∉ S) :
-- imply
  gvGlue η S τ x = η x := by
-- proof
  apply StatMech.Ising.gvGlue_not_mem η S τ hx

/--
[gvWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gvWeight_pos_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {S : Finset (Site d)}
-- given
  (β h : ℝ)
  (τ : {x // x ∈ S} → Bool) :
-- imply
  0 < gvWeight η S β h τ := by
-- proof
  apply StatMech.Ising.gvWeight_pos η S β h τ

/--
[gvZ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gvZ_pos_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {S : Finset (Site d)}
-- given
  (β h : ℝ) :
-- imply
  0 < gvZ η S β h := by
-- proof
  apply StatMech.Ising.gvZ_pos η S β h

/--
[gvZ_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gvZ_ne_zero_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {S : Finset (Site d)}
-- given
  (β h : ℝ) :
-- imply
  gvZ η S β h ≠ 0 := by
-- proof
  apply StatMech.Ising.gvZ_ne_zero η S β h

/--
[gvProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gvProb_nonneg_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {S : Finset (Site d)}
-- given
  (β h : ℝ)
  (τ : {x // x ∈ S} → Bool) :
-- imply
  0 ≤ gvProb η S β h τ := by
-- proof
  apply StatMech.Ising.gvProb_nonneg η S β h τ

/--
[gvProb_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gvProb_sum_eq_one_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {S : Finset (Site d)}
-- given
  (β h : ℝ) :
-- imply
  ∑ τ : {x // x ∈ S} → Bool, gvProb η S β h τ = 1 := by
-- proof
  apply StatMech.Ising.gvProb_sum_eq_one η S β h

/--
[gvMeasure_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gvMeasure_univ_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {S : Finset (Site d)}
-- given
  (β h : ℝ) :
-- imply
  (gvMeasure η S β h) Set.univ = 1 := by
-- proof
  apply StatMech.Ising.gvMeasure_univ η S β h

/--
[gvMeasure_real_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gvMeasure_real_eq_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {S : Finset (Site d)}
  {A : Set (ConfigSpace (Site d))}
-- given
  (β h : ℝ)
  (hA : MeasurableSet A) :
-- imply
  (gvMeasure η S β h).real A = ∑ τ : {x // x ∈ S} → Bool, gvProb η S β h τ * (Set.indicator A (fun _ => (1 : ℝ)) (gvGlue η S τ)) := by
-- proof
  apply StatMech.Ising.gvMeasure_real_eq η S β h hA

/--
[gvGlue_mono_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gvGlue_mono_interior_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {S : Finset (Site d)}
-- given
  (τ τ' : {x // x ∈ S} → Bool)
  (h : τ ≤ τ') :
-- imply
  gvGlue η S τ ≤ gvGlue η S τ' := by
-- proof
  apply StatMech.Ising.gvGlue_mono_interior η S τ τ' h

/--
[gvGlue_mono_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gvGlue_mono_boundary_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {η η' : ConfigSpace (Site d)}
-- given
  (hle : η ≤ η')
  (τ : {x // x ∈ S} → Bool) :
-- imply
  gvGlue η S τ ≤ gvGlue η' S τ := by
-- proof
  apply StatMech.Ising.gvGlue_mono_boundary S η η' hle τ

/--
[gv_spin_glue_inf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gv_spin_glue_inf_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {η η' : ConfigSpace (Site d)}
  {x : Site d}
-- given
  (hle : η ≤ η')
  (a b : {x // x ∈ S} → Bool) :
-- imply
  spin (gvGlue η S (a ⊓ b)) x = min (spin (gvGlue η S a) x) (spin (gvGlue η' S b) x) := by
-- proof
  apply StatMech.Ising.gv_spin_glue_inf S η η' hle a b x

/--
[gv_spin_glue_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gv_spin_glue_sup_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {η η' : ConfigSpace (Site d)}
  {x : Site d}
-- given
  (hle : η ≤ η')
  (a b : {x // x ∈ S} → Bool) :
-- imply
  spin (gvGlue η' S (a ⊔ b)) x = max (spin (gvGlue η S a) x) (spin (gvGlue η' S b) x) := by
-- proof
  apply StatMech.Ising.gv_spin_glue_sup S η η' hle a b x

/--
[gv_bond_glue_supermod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gv_bond_glue_supermod_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {η η' : ConfigSpace (Site d)}
  {e : Sym2 (Site d)}
-- given
  (hle : η ≤ η')
  (a b : {x // x ∈ S} → Bool) :
-- imply
  bond (gvGlue η S a) e + bond (gvGlue η' S b) e ≤ bond (gvGlue η S (a ⊓ b)) e + bond (gvGlue η' S (a ⊔ b)) e := by
-- proof
  apply StatMech.Ising.gv_bond_glue_supermod S η η' hle a b e

/--
[gv_spin_glue_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gv_spin_glue_add_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {η η' : ConfigSpace (Site d)}
  {x : Site d}
-- given
  (hle : η ≤ η')
  (a b : {x // x ∈ S} → Bool) :
-- imply
  spin (gvGlue η S a) x + spin (gvGlue η' S b) x = spin (gvGlue η S (a ⊓ b)) x + spin (gvGlue η' S (a ⊔ b)) x := by
-- proof
  apply StatMech.Ising.gv_spin_glue_add S η η' hle a b x

/--
[gv_fvEnergy_supermod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gv_fvEnergy_supermod_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {η η' : ConfigSpace (Site d)}
-- given
  (h : ℝ)
  (hh : 0 ≤ h)
  (hle : η ≤ η')
  (a b : {x // x ∈ S} → Bool) :
-- imply
  gvEnergy η S h (a ⊓ b) + gvEnergy η' S h (a ⊔ b) ≤ gvEnergy η S h a + gvEnergy η' S h b := by
-- proof
  apply StatMech.Ising.gv_fvEnergy_supermod S h hh η η' hle a b

/--
[gv_fvWeight_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gv_fvWeight_cross_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {β : ℝ}
  {η η' : ConfigSpace (Site d)}
-- given
  (hβ : 0 ≤ β)
  (h : ℝ)
  (hh : 0 ≤ h)
  (hle : η ≤ η')
  (a b : {x // x ∈ S} → Bool) :
-- imply
  gvWeight η S β h a * gvWeight η' S β h b ≤ gvWeight η S β h (a ⊓ b) * gvWeight η' S β h (a ⊔ b) := by
-- proof
  apply StatMech.Ising.gv_fvWeight_cross S hβ h hh η η' hle a b

/--
[gv_fvProb_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gv_fvProb_cross_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {β : ℝ}
  {η η' : ConfigSpace (Site d)}
-- given
  (hβ : 0 ≤ β)
  (h : ℝ)
  (hh : 0 ≤ h)
  (hle : η ≤ η')
  (a b : {x // x ∈ S} → Bool) :
-- imply
  gvProb η S β h a * gvProb η' S β h b ≤ gvProb η S β h (a ⊓ b) * gvProb η' S β h (a ⊔ b) := by
-- proof
  apply StatMech.Ising.gv_fvProb_cross S hβ h hh η η' hle a b

/--
[gv_fvProb_dominates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gv_fvProb_dominates_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {β : ℝ}
  {η η' : ConfigSpace (Site d)}
  {A : Set (ConfigSpace {x // x ∈ S})}
-- given
  (hβ : 0 ≤ β)
  (h : ℝ)
  (hh : 0 ≤ h)
  (hle : η ≤ η')
  (hA : IsIncreasing A) :
-- imply
  ∑ τ, A.indicator (fun _ => (1 : ℝ)) τ * gvProb η S β h τ ≤ ∑ τ, A.indicator (fun _ => (1 : ℝ)) τ * gvProb η' S β h τ := by
-- proof
  apply StatMech.Ising.gv_fvProb_dominates S hβ h hh η η' hle hA

/--
[gvMeasure_dominated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gvMeasure_dominated_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {β : ℝ}
  {h : ℝ}
  {η η' : ConfigSpace (Site d)}
  {A : Set (ConfigSpace (Site d))}
-- given
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hle : η ≤ η')
  (hA : MeasurableSet A)
  (hAinc : IsIncreasing A) :
-- imply
  (gvMeasure η S β h).real A ≤ (gvMeasure η' S β h).real A := by
-- proof
  apply StatMech.Ising.gvMeasure_dominated S hβ hh η η' hle hA hAinc

/--
[gv_le_plusField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gv_le_plusField_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)} :
-- imply
  η ≤ plusField d := by
-- proof
  apply StatMech.Ising.gv_le_plusField η

/--
[gvMeasure_le_plusField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gvMeasure_le_plusField_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {β : ℝ}
  {h : ℝ}
  {η : ConfigSpace (Site d)}
  {A : Set (ConfigSpace (Site d))}
-- given
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hA : MeasurableSet A)
  (hAinc : IsIncreasing A) :
-- imply
  (gvMeasure η S β h).real A ≤ (gvMeasure (plusField d) S β h).real A := by
-- proof
  apply StatMech.Ising.gvMeasure_le_plusField S hβ hh η hA hAinc

/--
[gvRes_gvOvr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gvRes_gvOvr_eq
  {d : ℕ}
  {Sin Sout : Finset (Site d)}
-- given
  (hsub : Sin ⊆ Sout)
  (σ : {x // x ∈ Sout} → Bool)
  (τ : {x // x ∈ Sin} → Bool) :
-- imply
  gvRes hsub (gvOvr hsub σ τ) = τ := by
-- proof
  apply StatMech.Ising.gvRes_gvOvr hsub σ τ

/--
[gvOvr_gvOvr_gvRes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gvOvr_gvOvr_gvRes_eq
  {d : ℕ}
  {Sin Sout : Finset (Site d)}
-- given
  (hsub : Sin ⊆ Sout)
  (σ : {x // x ∈ Sout} → Bool)
  (τ : {x // x ∈ Sin} → Bool) :
-- imply
  gvOvr hsub (gvOvr hsub σ τ) (gvRes hsub σ) = σ := by
-- proof
  apply StatMech.Ising.gvOvr_gvOvr_gvRes hsub σ τ

/--
[gvGlue_gvGlue_eq_gvGlue_ovr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gvGlue_gvGlue_eq_gvGlue_ovr_eq
  {d : ℕ}
  {Sin Sout : Finset (Site d)}
  {η : ConfigSpace (Site d)}
-- given
  (hsub : Sin ⊆ Sout)
  (σ : {x // x ∈ Sout} → Bool)
  (τ : {x // x ∈ Sin} → Bool) :
-- imply
  gvGlue (gvGlue η Sout σ) Sin τ = gvGlue η Sout (gvOvr hsub σ τ) := by
-- proof
  apply StatMech.Ising.gvGlue_gvGlue_eq_gvGlue_ovr hsub η σ τ

/--
[gvGlue_ovr_eq_off](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gvGlue_ovr_eq_off_eq
  {d : ℕ}
  {Sin Sout : Finset (Site d)}
  {η : ConfigSpace (Site d)}
  {x : Site d}
-- given
  (hsub : Sin ⊆ Sout)
  (σ : {x // x ∈ Sout} → Bool)
  (τ : {x // x ∈ Sin} → Bool)
  (hx : x ∉ Sin) :
-- imply
  gvGlue η Sout (gvOvr hsub σ τ) x = gvGlue η Sout σ x := by
-- proof
  apply StatMech.Ising.gvGlue_ovr_eq_off hsub η σ τ hx

/--
[gv_bond_glue_ovr_eq_of_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gv_bond_glue_ovr_eq_of_notMem_eq
  {d : ℕ}
  {Sin Sout : Finset (Site d)}
  {η : ConfigSpace (Site d)}
  {e : Sym2 (Site d)}
-- given
  (hsub : Sin ⊆ Sout)
  (σ : {x // x ∈ Sout} → Bool)
  (τ : {x // x ∈ Sin} → Bool)
  (heE : e ∈ (hypercubicLattice d).edgeSet)
  (heB : e ∉ gvBondTouch Sin) :
-- imply
  bond (gvGlue η Sout (gvOvr hsub σ τ)) e = bond (gvGlue η Sout σ) e := by
-- proof
  apply StatMech.Ising.gv_bond_glue_ovr_eq_of_notMem hsub η σ τ heE heB

/--
[gv_bond_sum_diff_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gv_bond_sum_diff_eq_eq
  {d : ℕ}
  {Sin Sout : Finset (Site d)}
  {η : ConfigSpace (Site d)}
-- given
  (hsub : Sin ⊆ Sout)
  (σ : {x // x ∈ Sout} → Bool)
  (τ : {x // x ∈ Sin} → Bool) :
-- imply
  (∑ e ∈ gvBondTouch Sout, bond (gvGlue η Sout (gvOvr hsub σ τ)) e) - (∑ e ∈ gvBondTouch Sout, bond (gvGlue η Sout σ) e) = (∑ e ∈ gvBondTouch Sin, bond (gvGlue η Sout (gvOvr hsub σ τ)) e) - (∑ e ∈ gvBondTouch Sin, bond (gvGlue η Sout σ) e) := by
-- proof
  apply StatMech.Ising.gv_bond_sum_diff_eq hsub η σ τ

/--
[gv_spin_sum_diff_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gv_spin_sum_diff_eq_eq
  {d : ℕ}
  {Sin Sout : Finset (Site d)}
  {η : ConfigSpace (Site d)}
-- given
  (hsub : Sin ⊆ Sout)
  (σ : {x // x ∈ Sout} → Bool)
  (τ : {x // x ∈ Sin} → Bool) :
-- imply
  (∑ x ∈ Sout, spin (gvGlue η Sout (gvOvr hsub σ τ)) x) - (∑ x ∈ Sout, spin (gvGlue η Sout σ) x) = (∑ x ∈ Sin, spin (gvGlue η Sout (gvOvr hsub σ τ)) x) - (∑ x ∈ Sin, spin (gvGlue η Sout σ) x) := by
-- proof
  apply StatMech.Ising.gv_spin_sum_diff_eq hsub η σ τ

/--
[gv_energy_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gv_energy_decomp_eq
  {d : ℕ}
  {Sin Sout : Finset (Site d)}
  {η : ConfigSpace (Site d)}
-- given
  (hsub : Sin ⊆ Sout)
  (h : ℝ)
  (σ : {x // x ∈ Sout} → Bool)
  (τ : {x // x ∈ Sin} → Bool) :
-- imply
  gvEnergy η Sout h σ + gvEnergy (gvGlue η Sout σ) Sin h τ = gvEnergy η Sout h (gvOvr hsub σ τ) + gvEnergy (gvGlue η Sout (gvOvr hsub σ τ)) Sin h (gvRes hsub σ) := by
-- proof
  apply StatMech.Ising.gv_energy_decomp hsub η h σ τ

/--
[gv_weight_spec_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gv_weight_spec_symm_eq
  {d : ℕ}
  {Sin Sout : Finset (Site d)}
  {η : ConfigSpace (Site d)}
-- given
  (hsub : Sin ⊆ Sout)
  (β h : ℝ)
  (σ : {x // x ∈ Sout} → Bool)
  (τ : {x // x ∈ Sin} → Bool) :
-- imply
  gvWeight η Sout β h σ * gvWeight (gvGlue η Sout σ) Sin β h τ = gvWeight η Sout β h (gvOvr hsub σ τ) * gvWeight (gvGlue η Sout (gvOvr hsub σ τ)) Sin β h (gvRes hsub σ) := by
-- proof
  apply StatMech.Ising.gv_weight_spec_symm hsub η β h σ τ

/--
[gv_fvWeight_eq_of_agree_off](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gv_fvWeight_eq_of_agree_off_eq
  {d : ℕ}
  {Sin : Finset (Site d)}
  {ζ₁ ζ₂ : ConfigSpace (Site d)}
-- given
  (β h : ℝ)
  (hagree : ∀ x ∉ Sin, ζ₁ x = ζ₂ x)
  (τ : {x // x ∈ Sin} → Bool) :
-- imply
  gvWeight ζ₁ Sin β h τ = gvWeight ζ₂ Sin β h τ := by
-- proof
  apply StatMech.Ising.gv_fvWeight_eq_of_agree_off β h hagree τ

/--
[gv_fvZ_eq_of_agree_off](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gv_fvZ_eq_of_agree_off_eq
  {d : ℕ}
  {Sin : Finset (Site d)}
  {ζ₁ ζ₂ : ConfigSpace (Site d)}
-- given
  (β h : ℝ)
  (hagree : ∀ x ∉ Sin, ζ₁ x = ζ₂ x) :
-- imply
  gvZ ζ₁ Sin β h = gvZ ζ₂ Sin β h := by
-- proof
  apply StatMech.Ising.gv_fvZ_eq_of_agree_off β h hagree

/--
[gvSwapPair_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gvSwapPair_involutive_eq
  {d : ℕ}
  {Sin Sout : Finset (Site d)}
-- given
  (hsub : Sin ⊆ Sout) :
-- imply
  Function.Involutive (gvSwapPair (d := d) hsub) := by
-- proof
  apply StatMech.Ising.gvSwapPair_involutive hsub

/--
[gvSwapPair_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gvSwapPair_bijective_eq
  {d : ℕ}
  {Sin Sout : Finset (Site d)}
-- given
  (hsub : Sin ⊆ Sout) :
-- imply
  Function.Bijective (gvSwapPair (d := d) hsub) := by
-- proof
  apply StatMech.Ising.gvSwapPair_bijective hsub

/--
[gv_consistency_double_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma gv_consistency_double_sum_eq
  {d : ℕ}
  {Sin Sout : Finset (Site d)}
  {η : ConfigSpace (Site d)}
  {g : ConfigSpace (Site d) → ℝ}
-- given
  (hsub : Sin ⊆ Sout)
  (β h : ℝ) :
-- imply
  (∑ σ : {x // x ∈ Sout} → Bool, gvProb η Sout β h σ * ∑ τ : {x // x ∈ Sin} → Bool, gvProb (gvGlue η Sout σ) Sin β h τ * g (gvGlue (gvGlue η Sout σ) Sin τ)) = ∑ σ : {x // x ∈ Sout} → Bool, gvProb η Sout β h σ * g (gvGlue η Sout σ) := by
-- proof
  apply StatMech.Ising.gv_consistency_double_sum hsub η β h g

/--
[iptp_gv_crossbox_dom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma iptp_gv_crossbox_dom_eq
  {d : ℕ}
  {Sin Sout : Finset (Site d)}
  {β : ℝ}
  {h : ℝ}
  {A : Set (ConfigSpace (Site d))}
-- given
  (hsub : Sin ⊆ Sout)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hAmeas : MeasurableSet A)
  (hAinc : IsIncreasing A) :
-- imply
  (gvPlusMeasure Sout β h).real A ≤ (gvPlusMeasure Sin β h).real A := by
-- proof
  apply StatMech.Ising.iptp_gv_crossbox_dom hsub hβ hh hAmeas hAinc

/--
[iptp_gvBondTouch_boxFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma iptp_gvBondTouch_boxFinset_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  gvBondTouch (boxFinset d n) = bondFinsetTouch d n := by
-- proof
  apply StatMech.Ising.iptp_gvBondTouch_boxFinset n

/--
[iptp_gvGlue_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma iptp_gvGlue_box_eq
  {d : ℕ}
  {n : ℕ}
  {η : ConfigSpace (Site d)}
-- given
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  gvGlue η (boxFinset d n) (fun y => τ ((iptp_boxEquiv d n).symm y)) = glue η τ := by
-- proof
  apply StatMech.Ising.iptp_gvGlue_box n η τ

/--
[iptp_gvEnergy_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma iptp_gvEnergy_box_eq
  {d : ℕ}
  {n : ℕ}
  {η : ConfigSpace (Site d)}
-- given
  (h : ℝ)
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  gvEnergy η (boxFinset d n) h (fun y => τ ((iptp_boxEquiv d n).symm y)) = fvEnergy η n (bondFinsetTouch d n) h τ := by
-- proof
  apply StatMech.Ising.iptp_gvEnergy_box n η h τ

/--
[iptp_gvWeight_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma iptp_gvWeight_box_eq
  {d : ℕ}
  {n : ℕ}
  {η : ConfigSpace (Site d)}
-- given
  (β h : ℝ)
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  gvWeight η (boxFinset d n) β h (fun y => τ ((iptp_boxEquiv d n).symm y)) = fvWeight η n (bondFinsetTouch d n) β h τ := by
-- proof
  apply StatMech.Ising.iptp_gvWeight_box n η β h τ

/--
[iptp_gvZ_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma iptp_gvZ_box_eq
  {d : ℕ}
  {n : ℕ}
  {η : ConfigSpace (Site d)}
-- given
  (β h : ℝ) :
-- imply
  gvZ η (boxFinset d n) β h = fvZ η n (bondFinsetTouch d n) β h := by
-- proof
  apply StatMech.Ising.iptp_gvZ_box n η β h

/--
[iptp_gvProb_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma iptp_gvProb_box_eq
  {d : ℕ}
  {n : ℕ}
  {η : ConfigSpace (Site d)}
-- given
  (β h : ℝ)
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  gvProb η (boxFinset d n) β h (fun y => τ ((iptp_boxEquiv d n).symm y)) = fvProb η n (bondFinsetTouch d n) β h τ := by
-- proof
  apply StatMech.Ising.iptp_gvProb_box n η β h τ

/--
[iptp_gvMeasure_eq_fvMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma iptp_gvMeasure_eq_fvMeasure_eq
  {d : ℕ}
  {n : ℕ}
  {η : ConfigSpace (Site d)}
-- given
  (β h : ℝ) :
-- imply
  gvMeasure η (boxFinset d n) β h = fvMeasure η n (bondFinsetTouch d n) β h := by
-- proof
  apply StatMech.Ising.iptp_gvMeasure_eq_fvMeasure n η β h

/--
[iptp_gvPlusMeasure_eq_plusMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma iptp_gvPlusMeasure_eq_plusMeasure_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (β h : ℝ) :
-- imply
  gvPlusMeasure (boxFinset d n) β h = (plusMeasure d n β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.iptp_gvPlusMeasure_eq_plusMeasure n β h

/--
[iptp_gvBondTouch_image_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma iptp_gvBondTouch_image_subset_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {S : Finset (Site d)} :
-- imply
  (gvBondTouch S).image (fun e => g • e) ⊆ gvBondTouch (S.image (fun x => g • x)) := by
-- proof
  apply StatMech.Ising.iptp_gvBondTouch_image_subset g S

/--
[iptp_gvBondTouch_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma iptp_gvBondTouch_image_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {S : Finset (Site d)} :
-- imply
  gvBondTouch (S.image (fun x => g • x)) = (gvBondTouch S).image (fun e => g • e) := by
-- proof
  apply StatMech.Ising.iptp_gvBondTouch_image g S

/--
[iptp_gvGlue_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma iptp_gvGlue_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {S : Finset (Site d)}
-- given
  (τ : {x // x ∈ S} → Bool) :
-- imply
  ConfigSpace.shift g (gvGlue (plusField d) S τ) = gvGlue (plusField d) (S.image (fun x => g • x)) (fun y => τ ((iptp_transInteriorEquiv g S).symm y)) := by
-- proof
  apply StatMech.Ising.iptp_gvGlue_shift g S τ

/--
[iptp_spin_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma iptp_spin_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {c : ConfigSpace (Site d)}
  {x : Site d} :
-- imply
  spin (ConfigSpace.shift g c) (g • x) = spin c x := by
-- proof
  apply StatMech.Ising.iptp_spin_shift g c x

/--
[iptp_bond_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma iptp_bond_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {c : ConfigSpace (Site d)}
  {e : Sym2 (Site d)} :
-- imply
  bond (ConfigSpace.shift g c) (g • e) = bond c e := by
-- proof
  apply StatMech.Ising.iptp_bond_shift g c e

/--
[iptp_gvEnergy_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma iptp_gvEnergy_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {S : Finset (Site d)}
-- given
  (h : ℝ)
  (τ : {x // x ∈ S} → Bool) :
-- imply
  gvEnergy (plusField d) (S.image (fun x => g • x)) h (fun y => τ ((iptp_transInteriorEquiv g S).symm y)) = gvEnergy (plusField d) S h τ := by
-- proof
  apply StatMech.Ising.iptp_gvEnergy_shift g S h τ

/--
[iptp_gvWeight_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma iptp_gvWeight_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {S : Finset (Site d)}
-- given
  (β h : ℝ)
  (τ : {x // x ∈ S} → Bool) :
-- imply
  gvWeight (plusField d) (S.image (fun x => g • x)) β h (fun y => τ ((iptp_transInteriorEquiv g S).symm y)) = gvWeight (plusField d) S β h τ := by
-- proof
  apply StatMech.Ising.iptp_gvWeight_shift g S β h τ

/--
[iptp_gvZ_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma iptp_gvZ_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {S : Finset (Site d)}
-- given
  (β h : ℝ) :
-- imply
  gvZ (plusField d) (S.image (fun x => g • x)) β h = gvZ (plusField d) S β h := by
-- proof
  apply StatMech.Ising.iptp_gvZ_shift g S β h

/--
[iptp_gvProb_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma iptp_gvProb_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {S : Finset (Site d)}
-- given
  (β h : ℝ)
  (τ : {x // x ∈ S} → Bool) :
-- imply
  gvProb (plusField d) (S.image (fun x => g • x)) β h (fun y => τ ((iptp_transInteriorEquiv g S).symm y)) = gvProb (plusField d) S β h τ := by
-- proof
  apply StatMech.Ising.iptp_gvProb_shift g S β h τ

/--
[iptp_map_sum_aux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma iptp_map_sum_aux_eq
  {d : ℕ}
  [Fintype ι]
  {f : ConfigSpace (Site d) → ConfigSpace (Site d)}
  {μ : ι → Measure (ConfigSpace (Site d))}
-- given
  (hf : Measurable f) :
-- imply
  Measure.map f (∑ i, μ i) = ∑ i, Measure.map f (μ i) := by
-- proof
  apply StatMech.Ising.iptp_map_sum_aux f hf μ

/--
[iptp_gvMeasure_map_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma iptp_gvMeasure_map_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {S : Finset (Site d)}
-- given
  (β h : ℝ) :
-- imply
  Measure.map (ConfigSpace.shift g) (gvMeasure (plusField d) S β h) = gvMeasure (plusField d) (S.image (fun x => g • x)) β h := by
-- proof
  apply StatMech.Ising.iptp_gvMeasure_map_shift g S β h

/--
[iptp_gvPlus_real_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma iptp_gvPlus_real_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {S : Finset (Site d)}
  {T : Finset (Site d)}
-- given
  (β h : ℝ) :
-- imply
  (gvPlusMeasure (S.image (fun x => g • x)) β h).real (fmu_multiOpen T) = (gvPlusMeasure S β h).real (fmu_multiOpen (T.image (fun e => g⁻¹ • e))) := by
-- proof
  apply StatMech.Ising.iptp_gvPlus_real_shift g S β h T

/--
[iptp_inv_smul_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma iptp_inv_smul_coord_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {y : Site d}
  {i : Fin d} :
-- imply
  (g⁻¹ • y) i = y i - Multiplicative.toAdd g i := by
-- proof
  apply StatMech.Ising.iptp_inv_smul_coord g y i

/--
[iptp_box_subset_transBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma iptp_box_subset_transBox_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {a m : ℕ}
-- given
  (hcm : a + flc_vrad (Multiplicative.toAdd g) ≤ m) :
-- imply
  boxFinset d a ⊆ (boxFinset d m).image (fun x => g • x) := by
-- proof
  apply StatMech.Ising.iptp_box_subset_transBox g hcm

/--
[iptp_transBox_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma iptp_transBox_subset_box_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {m : ℕ} :
-- imply
  (boxFinset d m).image (fun x => g • x) ⊆ boxFinset d (m + flc_vrad (Multiplicative.toAdd g)) := by
-- proof
  apply StatMech.Ising.iptp_transBox_subset_box g m

/--
[iptp_squeeze_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma iptp_squeeze_lower_eq
  {d : ℕ}
  {β : ℝ}
  {h : ℝ}
  {g : Multiplicative (Site d)}
  {T : Finset (Site d)}
  {m : ℕ}
-- given
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  (plusMeasure d (m + flc_vrad (Multiplicative.toAdd g)) β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen (E := Site d) T) ≤ (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen (E := Site d) (T.image (fun x => g⁻¹ • x))) := by
-- proof
  apply StatMech.Ising.iptp_squeeze_lower hβ hh g T m

/--
[iptp_squeeze_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma iptp_squeeze_upper_eq
  {d : ℕ}
  {β : ℝ}
  {h : ℝ}
  {g : Multiplicative (Site d)}
  {T : Finset (Site d)}
  {a m : ℕ}
-- given
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hcond : a + flc_vrad (Multiplicative.toAdd g) ≤ m) :
-- imply
  (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen (E := Site d) (T.image (fun x => g⁻¹ • x))) ≤ (plusMeasure d a β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen (E := Site d) T) := by
-- proof
  apply StatMech.Ising.iptp_squeeze_upper hβ hh g T hcond

/--
[iptp_plusMultiHomogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma iptp_plusMultiHomogeneous_eq
  {d : ℕ}
  {β : ℝ}
  {h : ℝ}
  {g : Multiplicative (Site d)}
-- given
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  iti_PlusMultiHomogeneous β h g := by
-- proof
  apply StatMech.Ising.iptp_plusMultiHomogeneous hβ hh g

/--
[iptp_plusState_isTranslationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma iptp_plusState_isTranslationInvariant_eq
  {d : ℕ}
  {β : ℝ}
  {h : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.iptp_plusState_isTranslationInvariant hβ hh

/--
[ising_plus_extreme](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma ising_plus_extreme_eq
  {d : ℕ}
  {β : ℝ}
  {h : ℝ}
-- given
  (hd : 1 ≤ d)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  StatMech.FK.IsInvariantExtremePoint (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.ising_plus_extreme hd hβ hh

/--
[iptp_plusState_isErgodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean)
-/
@[path]
private lemma iptp_plusState_isErgodic_eq
  {d : ℕ}
  {β : ℝ}
  {h : ℝ}
-- given
  (hd : 1 ≤ d)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.iptp_plusState_isErgodic hd hβ hh


-- created on 2026-10-23
