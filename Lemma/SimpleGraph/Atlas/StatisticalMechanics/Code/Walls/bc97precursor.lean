import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc97precursor.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc97_boundaryGenuine_subset_vertexBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc97precursor.lean)
-/
@[path]
private lemma bc97_boundaryGenuine_subset_vertexBoundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  bc97_boundaryGenuineFinset ω n ⊆ (vertexBoundary_finite d n).toFinset := by
-- proof
  apply StatMech.Walls.bc97_boundaryGenuine_subset_vertexBoundary ω n

/--
[bc97_boundary_genuineCount_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc97precursor.lean)
-/
@[path]
private lemma bc97_boundary_genuineCount_le_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  (bc97_boundaryGenuineFinset ω n).card ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc97_boundary_genuineCount_le ω n

/--
[bc97_genuineCount_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc97precursor.lean)
-/
@[path]
private lemma bc97_genuineCount_split_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  bc89_genuineTcount ω n = (bc97_interiorGenuineFinset ω n).card + (bc97_boundaryGenuineFinset ω n).card := by
-- proof
  apply StatMech.Walls.bc97_genuineCount_split ω n

/--
[bc97_genuineCount_le_interior_plus_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc97precursor.lean)
-/
@[path]
private lemma bc97_genuineCount_le_interior_plus_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  bc89_genuineTcount ω n ≤ (bc97_interiorGenuineFinset ω n).card + boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc97_genuineCount_le_interior_plus_boundary ω n

/--
[bc97_interior_harmbox_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc97precursor.lean)
-/
@[path]
private lemma bc97_interior_harmbox_free_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d}
  {a : Site d}
-- given
  (hn : 1 ≤ n)
  (hxint : x ∈ box d (n - 1))
  (hadj : (openSubgraph d ω).Adj x a) :
-- imply
  a ∈ box d n := by
-- proof
  apply StatMech.Walls.bc97_interior_harmbox_free ω hn hxint hadj

/--
[bc97_forceOrigin_genuineTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc97precursor.lean)
-/
@[path]
private lemma bc97_forceOrigin_genuineTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a₁ a₂ a₃ x₁ x₂ x₃ : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧ (hypercubicLattice d).Adj 0 a₃)
  (hconn : Connected d (removeSite 0 ω) a₁ x₁ ∧ Connected d (removeSite 0 ω) a₂ x₂ ∧ Connected d (removeSite 0 ω) a₃ x₃)
  (hinf : (cluster d (removeSite 0 ω) x₁).Infinite ∧ (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite)
  (hdist : cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₂ ∧ cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₃ ∧ cluster d (removeSite 0 ω) x₂ ≠ cluster d (removeSite 0 ω) x₃) :
-- imply
  bc89_GenuineTrif d (forceOpenFinset {s((0 : Site d), a₁), s(0, a₂), s(0, a₃)} ω) 0 := by
-- proof
  apply StatMech.Walls.bc97_forceOrigin_genuineTrif ω hadj hconn hinf hdist

/--
[bc97_precursor_subset_force_genuineTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc97precursor.lean)
-/
@[path]
private lemma bc97_precursor_subset_force_genuineTrif_eq
  {d : ℕ}
  {a₁ a₂ a₃ x₁ x₂ x₃ : Site d} :
-- imply
  bc97_SingleSitePrecursor d a₁ a₂ a₃ x₁ x₂ x₃ ⊆ (fun ω => forceOpenFinset {s((0 : Site d), a₁), s(0, a₂), s(0, a₃)} ω) ⁻¹' {ω | bc89_GenuineTrif d ω 0} := by
-- proof
  apply StatMech.Walls.bc97_precursor_subset_force_genuineTrif a₁ a₂ a₃ x₁ x₂ x₃

/--
[bc97_close_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc97precursor.lean)
-/
@[path]
private lemma bc97_close_a_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hroute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ x₁ x₂ x₃ : Site d, 0 < μ (bc97_SingleSitePrecursor d a₁ a₂ a₃ x₁ x₂ x₃)) :
-- imply
  bc95_SingleSiteRewiring μ := by
-- proof
  apply StatMech.Walls.bc97_close_a μ hfe hroute

/--
[bc97_bk_from_route](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc97precursor.lean)
-/
@[path]
private lemma bc97_bk_from_route_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hprob0 : μ {ω | bc89_GenuineTrif d ω 0} = 0)
  (hroute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ x₁ x₂ x₃ : Site d, 0 < μ (bc97_SingleSitePrecursor d a₁ a₂ a₃ x₁ x₂ x₃)) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc97_bk_from_route μ hfe hprob0 hroute

/--
[bc97_full_count_of_global_harmbox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc97precursor.lean)
-/
@[path]
private lemma bc97_full_count_of_global_harmbox_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → bc89_GenuineTrif d ω x)
  (harmbox : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n) :
-- imply
  bc89_genuineTcount ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc97_full_count_of_global_harmbox ω n hn hcanon harmbox

/--
[bc97_upperLines_boundary_count_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc97precursor.lean)
-/
@[path]
private lemma bc97_upperLines_boundary_count_zero_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  (bc97_boundaryGenuineFinset bc60_upperLines n).card = 0 ∧ (bc97_interiorGenuineFinset bc60_upperLines n).card = 0 := by
-- proof
  apply StatMech.Walls.bc97_upperLines_boundary_count_zero n

/--
[bc97_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc97precursor.lean)
-/
@[path]
private lemma bc97_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site 2))) {a₁ a₂ a₃ x₁ x₂ x₃ : Site 2}, ((hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧ (hypercubicLattice 2).Adj 0 a₃) → (Connected 2 (removeSite 0 ω) a₁ x₁ ∧ Connected 2 (removeSite 0 ω) a₂ x₂ ∧ Connected 2 (removeSite 0 ω) a₃ x₃) → ((cluster 2 (removeSite 0 ω) x₁).Infinite ∧ (cluster 2 (removeSite 0 ω) x₂).Infinite ∧ (cluster 2 (removeSite 0 ω) x₃).Infinite) → (cluster 2 (removeSite 0 ω) x₁ ≠ cluster 2 (removeSite 0 ω) x₂ ∧ cluster 2 (removeSite 0 ω) x₁ ≠ cluster 2 (removeSite 0 ω) x₃ ∧ cluster 2 (removeSite 0 ω) x₂ ≠ cluster 2 (removeSite 0 ω) x₃) → bc89_GenuineTrif 2 (forceOpenFinset {s((0 : Site 2), a₁), s(0, a₂), s(0, a₃)} ω) 0) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ], HasFiniteEnergyMerge μ → (0 < μ {ω | numInfiniteClusters 2 ω = ⊤} → ∃ a₁ a₂ a₃ x₁ x₂ x₃ : Site 2, 0 < μ (bc97_SingleSitePrecursor 2 a₁ a₂ a₃ x₁ x₂ x₃)) → bc95_SingleSiteRewiring μ) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ], HasFiniteEnergyMerge μ → μ {ω | bc89_GenuineTrif 2 ω 0} = 0 → (0 < μ {ω | numInfiniteClusters 2 ω = ⊤} → ∃ a₁ a₂ a₃ x₁ x₂ x₃ : Site 2, 0 < μ (bc97_SingleSitePrecursor 2 a₁ a₂ a₃ x₁ x₂ x₃)) → μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), (bc97_boundaryGenuineFinset ω n).card ≤ boxSV_boundaryCard 2 n) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), bc89_genuineTcount ω n ≤ (bc97_interiorGenuineFinset ω n).card + boxSV_boundaryCard 2 n) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), 1 ≤ n → (∀ x, x ∈ box 2 n → IsTrifurcation 2 ω x → bc89_GenuineTrif 2 ω x) → (∀ x, x ∈ box 2 n → IsTrifurcation 2 ω x → ∀ a, (openSubgraph 2 ω).Adj x a → (cluster 2 (removeSite x ω) a).Infinite → a ∈ box 2 n) → bc89_genuineTcount ω n ≤ boxSV_boundaryCard 2 n) := by
-- proof
  apply StatMech.Walls.bc97_status


-- created on 2026-10-23
