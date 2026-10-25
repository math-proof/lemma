import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc99connect
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc99_texBoxAttach_of_bmm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc99connect.lean)
-/
@[path]
private lemma bc99_texBoxAttach_of_bmm_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : bmm_BoxMengerAttachment d n) :
-- imply
  tex_BoxAttachData d n := by
-- proof
  apply StatMech.Walls.bc99_texBoxAttach_of_bmm h

/--
[bc99_texBoxAttach_of_reachesNbr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc99connect.lean)
-/
@[path]
private lemma bc99_texBoxAttach_of_reachesNbr_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : bc56_BoxClusterReachesNbr d n) :
-- imply
  tex_BoxAttachData d n := by
-- proof
  apply StatMech.Walls.bc99_texBoxAttach_of_reachesNbr h

/--
[bc99_hroute_of_reachesNbr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc99connect.lean)
-/
@[path]
private lemma bc99_hroute_of_reachesNbr_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (h : ∀ n : ℕ, bc56_BoxClusterReachesNbr d n) :
-- imply
  0 < μ {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ x₁ x₂ x₃ : Site d, 0 < μ (bc97_SingleSitePrecursor d a₁ a₂ a₃ x₁ x₂ x₃) := by
-- proof
  apply StatMech.Walls.bc99_hroute_of_reachesNbr μ hfe h

/--
[bc99_close_a_of_reachesNbr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc99connect.lean)
-/
@[path]
private lemma bc99_close_a_of_reachesNbr_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (h : ∀ n : ℕ, bc56_BoxClusterReachesNbr d n) :
-- imply
  bc95_SingleSiteRewiring μ := by
-- proof
  apply StatMech.Walls.bc99_close_a_of_reachesNbr μ hfe h

/--
[bc99_bk_from_reachesNbr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc99connect.lean)
-/
@[path]
private lemma bc99_bk_from_reachesNbr_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hprob0 : μ {ω | bc89_GenuineTrif d ω 0} = 0)
  (h : ∀ n : ℕ, bc56_BoxClusterReachesNbr d n) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc99_bk_from_reachesNbr μ hfe hprob0 h

/--
[bc99_upperLines_cluster_height](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc99connect.lean)
-/
@[path]
private lemma bc99_upperLines_cluster_height_eq
  {d : ℕ}
  {h : ℤ}
  {a : Site 2}
-- given
  (ha : a ∈ cluster 2 bc60_upperLines (bc57_pt 0 h)) :
-- imply
  a 1 = h := by
-- proof
  apply StatMech.Walls.bc99_upperLines_cluster_height ha

/--
[bc99_reachesNbr_fails_upperLines](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc99connect.lean)
-/
@[path]
private lemma bc99_reachesNbr_fails_upperLines_eq
  {d : ℕ} :
-- imply
  ¬ bc56_ClusterReachesNbr bc60_upperLines (bc57_pt 0 3) := by
-- proof
  apply StatMech.Walls.bc99_reachesNbr_fails_upperLines

/--
[bc99_boxReachesNbr_fails](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc99connect.lean)
-/
@[path]
private lemma bc99_boxReachesNbr_fails_eq
  {d : ℕ} :
-- imply
  ¬ bc56_BoxClusterReachesNbr 2 3 := by
-- proof
  apply StatMech.Walls.bc99_boxReachesNbr_fails

/--
[bc99_notFree_of_coarseTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc99connect.lean)
-/
@[path]
private lemma bc99_notFree_of_coarseTrif_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) ∧ ¬ bc56_BoxClusterReachesNbr 2 3 := by
-- proof
  apply StatMech.Walls.bc99_notFree_of_coarseTrif hL

/--
[bc99_reachesNbr_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc99connect.lean)
-/
@[path]
private lemma bc99_reachesNbr_nonvacuous_eq
  {d : ℕ} :
-- imply
  bc56_ClusterReachesNbr CtcWitness.threeRayConfig (CtcWitness.px 1) := by
-- proof
  apply StatMech.Walls.bc99_reachesNbr_nonvacuous

/--
[bc99_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc99connect.lean)
-/
@[path]
private lemma bc99_status_eq
  {d : ℕ} :
-- imply
  (∀ (n : ℕ), bc56_BoxClusterReachesNbr 2 n → tex_BoxAttachData 2 n) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ], HasFiniteEnergyMerge μ → μ {ω | bc89_GenuineTrif 2 ω 0} = 0 → (∀ n : ℕ, bc56_BoxClusterReachesNbr 2 n) → μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) ∧ (∀ (L : ℕ), 3 ≤ L → bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) ∧ ¬ bc56_BoxClusterReachesNbr 2 3) ∧ bc56_ClusterReachesNbr CtcWitness.threeRayConfig (CtcWitness.px 1) := by
-- proof
  apply StatMech.Walls.bc99_status


-- created on 2026-10-23
