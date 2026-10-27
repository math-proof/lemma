import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationConstruction.Part3
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[removeSite_forceOpen_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationConstruction.lean)
-/
@[path]
private lemma removeSite_forceOpen_eq_eq
  {d : ℕ}
  {x : Site d}
  {F : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hF : ∀ e ∈ F, x ∈ e) :
-- imply
  removeSite x (forceOpenFinset F ω) = removeSite x ω := by
-- proof
  apply StatMech.Percolation.removeSite_forceOpen_eq x F hF ω

/--
[removeSite_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationConstruction.lean)
-/
@[path]
private lemma removeSite_le_eq
  {d : ℕ}
  {x : Site d}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  removeSite x ω ≤ ω := by
-- proof
  apply StatMech.Percolation.removeSite_le x ω

/--
[isTrifurcation_of_neighbors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationConstruction.lean)
-/
@[path]
private lemma isTrifurcation_of_neighbors_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a₁ a₂ a₃ : Site d}
-- given
  (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
  (hadj1 : (hypercubicLattice d).Adj 0 a₁)
  (hadj2 : (hypercubicLattice d).Adj 0 a₂)
  (hadj3 : (hypercubicLattice d).Adj 0 a₃)
  (hinf1 : (cluster d (removeSite 0 ω) a₁).Infinite)
  (hinf2 : (cluster d (removeSite 0 ω) a₂).Infinite)
  (hinf3 : (cluster d (removeSite 0 ω) a₃).Infinite)
  (hsep12 : ¬ Connected d (removeSite 0 ω) a₁ a₂)
  (hsep13 : ¬ Connected d (removeSite 0 ω) a₁ a₃)
  (hsep23 : ¬ Connected d (removeSite 0 ω) a₂ a₃) :
-- imply
  IsTrifurcation d (forceOpenFinset {s((0:Site d), a₁), s((0:Site d), a₂), s((0:Site d), a₃)} ω) 0 := by
-- proof
  apply StatMech.Percolation.isTrifurcation_of_neighbors ω a₁ a₂ a₃ hne hadj1 hadj2 hadj3 hinf1 hinf2 hinf3 hsep12 hsep13 hsep23

/--
[precursor_subset_force_trif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationConstruction.lean)
-/
@[path]
private lemma precursor_subset_force_trif_eq
  {d : ℕ}
  {a₁ a₂ a₃ : Site d} :
-- imply
  NeighborTrifPrecursor d a₁ a₂ a₃ ⊆ (fun ω => forceOpenFinset {s((0:Site d), a₁), s((0:Site d), a₂), s((0:Site d), a₃)} ω) ⁻¹' {ω | IsTrifurcation d ω 0} := by
-- proof
  apply StatMech.Percolation.precursor_subset_force_trif a₁ a₂ a₃

/--
[trif_pos_of_precursor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationConstruction.lean)
-/
@[path]
private lemma trif_pos_of_precursor_pos_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {a₁ a₂ a₃ : Site d}
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hpos : 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃)) :
-- imply
  0 < μ {ω | IsTrifurcation d ω 0} := by
-- proof
  apply StatMech.Percolation.trif_pos_of_precursor_pos μ hfe a₁ a₂ a₃ hpos

/--
[exists_three_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationConstruction.lean)
-/
@[path]
private lemma exists_three_distinct_eq
  {d : ℕ}
  {S : Set α}
-- given
  (h : S.encard = ⊤) :
-- imply
  ∃ a b c, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
-- proof
  apply StatMech.Percolation.exists_three_distinct h

/--
[iEqTop_subset_iUnion_threeMeetBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationConstruction.lean)
-/
@[path]
private lemma iEqTop_subset_iUnion_threeMeetBox_eq
  {d : ℕ} :
-- imply
  {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = ⊤} ⊆ ⋃ n, threeMeetBox d n := by
-- proof
  apply StatMech.Percolation.iEqTop_subset_iUnion_threeMeetBox

/--
[exists_threeMeetBox_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationConstruction.lean)
-/
@[path]
private lemma exists_threeMeetBox_pos_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hpos : 0 < μ {ω | numInfiniteClusters d ω = ⊤}) :
-- imply
  ∃ n : ℕ, 0 < μ (threeMeetBox d n) := by
-- proof
  apply StatMech.Percolation.exists_threeMeetBox_pos μ hpos

/--
[htrif_discharged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationConstruction.lean)
-/
@[path]
private lemma htrif_discharged_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hroute : ∀ n : ℕ, 0 < μ (threeMeetBox d n) → ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃)) :
-- imply
  0 < μ {ω | numInfiniteClusters d ω = ⊤} → 0 < μ {ω | IsTrifurcation d ω 0} := by
-- proof
  apply StatMech.Percolation.htrif_discharged μ hfe hroute

/--
[burton_keane_uniqueness_trif_route](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationConstruction.lean)
-/
@[path]
private lemma burton_keane_uniqueness_trif_route_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {bdry : ℕ → ℕ}
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
  (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
  (hdens : Filter.Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) Filter.atTop (nhds 0))
  (hroute : ∀ n : ℕ, 0 < μ (threeMeetBox d n) → ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃)) :
-- imply
  (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.burton_keane_uniqueness_trif_route μ herg hfe bdry hbound hvol hdens hroute


-- created on 2026-10-23
