import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc89genuinetrifae
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc89_genuine_imp_isTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc89genuinetrifae.lean)
-/
@[path]
private lemma bc89_genuine_imp_isTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (h : bc89_GenuineTrif d ω x) :
-- imply
  IsTrifurcation d ω x := by
-- proof
  apply StatMech.Walls.bc89_genuine_imp_isTrif ω x h

/--
[bc89_genuineTrifFinset_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc89genuinetrifae.lean)
-/
@[path]
private lemma bc89_genuineTrifFinset_subset_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  bc89_genuineTrifFinset ω n ⊆ tfc_trifFinset ω n := by
-- proof
  apply StatMech.Walls.bc89_genuineTrifFinset_subset ω n

/--
[bc89_genuineTcount_le_Tcount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc89genuinetrifae.lean)
-/
@[path]
private lemma bc89_genuineTcount_le_Tcount_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  bc89_genuineTcount ω n ≤ Tcount d ω n := by
-- proof
  apply StatMech.Walls.bc89_genuineTcount_le_Tcount ω n

/--
[bc89_removeSite_no_open_nbr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc89genuinetrifae.lean)
-/
@[path]
private lemma bc89_removeSite_no_open_nbr_eq
  {d : ℕ}
  {x y : Site d}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  ¬ (openSubgraph d (removeSite x ω)).Adj x y := by
-- proof
  apply StatMech.Walls.bc89_removeSite_no_open_nbr x y ω

/--
[bc89_removeSite_connected_center_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc89genuinetrifae.lean)
-/
@[path]
private lemma bc89_removeSite_connected_center_iff_eq
  {d : ℕ}
  {x y : Site d}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  Connected d (removeSite x ω) x y ↔ y = x := by
-- proof
  apply StatMech.Walls.bc89_removeSite_connected_center_iff x y ω

/--
[bc89_center_removeSite_cluster_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc89genuinetrifae.lean)
-/
@[path]
private lemma bc89_center_removeSite_cluster_eq_eq
  {d : ℕ}
  {x : Site d}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  cluster d (removeSite x ω) x = {x} := by
-- proof
  apply StatMech.Walls.bc89_center_removeSite_cluster_eq x ω

/--
[bc89_center_removeSite_cluster_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc89genuinetrifae.lean)
-/
@[path]
private lemma bc89_center_removeSite_cluster_finite_eq
  {d : ℕ}
  {x : Site d}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  ¬ (cluster d (removeSite x ω) x).Infinite := by
-- proof
  apply StatMech.Walls.bc89_center_removeSite_cluster_finite x ω

/--
[bc89_three_open_nbrs_of_genuine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc89genuinetrifae.lean)
-/
@[path]
private lemma bc89_three_open_nbrs_of_genuine_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (h : bc89_GenuineTrif d ω x) :
-- imply
  ∃ a₁ a₂ a₃ : Site d, (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧ (openSubgraph d ω).Adj x a₁ ∧ (openSubgraph d ω).Adj x a₂ ∧ (openSubgraph d ω).Adj x a₃ := by
-- proof
  apply StatMech.Walls.bc89_three_open_nbrs_of_genuine ω x h

/--
[bc89_genuineTrif_open_degree_ge_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc89genuinetrifae.lean)
-/
@[path]
private lemma bc89_genuineTrif_open_degree_ge_three_eq
  {d : ℕ}
  {Vset : Finset (Site d)}
  {F : SimpleGraph (↑Vset : Type)}
  [DecidableRel F.Adj]
  {vx : (↑Vset : Type)}
  {b : Fin 3 → (↑Vset : Type)}
-- given
  (hbne : b 0 ≠ b 1 ∧ b 0 ≠ b 2 ∧ b 1 ≠ b 2)
  (hnbr : ∀ i, F.Adj vx (b i)) :
-- imply
  3 ≤ F.degree vx := by
-- proof
  apply StatMech.Walls.bc89_genuineTrif_open_degree_ge_three F vx b hbne hnbr

/--
[bc89_upperLines_open_nbr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc89genuinetrifae.lean)
-/
@[path]
private lemma bc89_upperLines_open_nbr_eq
  {d : ℕ}
  {x v : Site 2}
-- given
  (hadj : (openSubgraph 2 bc60_upperLines).Adj x v) :
-- imply
  v 1 = x 1 ∧ (v 0 - x 0).natAbs = 1 := by
-- proof
  apply StatMech.Walls.bc89_upperLines_open_nbr hadj

/--
[bc89_upperLines_no_three_open_nbrs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc89genuinetrifae.lean)
-/
@[path]
private lemma bc89_upperLines_no_three_open_nbrs_eq
  {d : ℕ}
  {x a₁ a₂ a₃ : Site 2}
-- given
  (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
  (hadj : (openSubgraph 2 bc60_upperLines).Adj x a₁ ∧ (openSubgraph 2 bc60_upperLines).Adj x a₂ ∧ (openSubgraph 2 bc60_upperLines).Adj x a₃) :
-- imply
  False := by
-- proof
  apply StatMech.Walls.bc89_upperLines_no_three_open_nbrs x a₁ a₂ a₃ hne hadj

/--
[bc89_upperLines_not_genuineTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc89genuinetrifae.lean)
-/
@[path]
private lemma bc89_upperLines_not_genuineTrif_eq
  {d : ℕ}
  {x : Site 2} :
-- imply
  ¬ bc89_GenuineTrif 2 bc60_upperLines x := by
-- proof
  apply StatMech.Walls.bc89_upperLines_not_genuineTrif x

/--
[bc89_upperLines_genuineTcount_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc89genuinetrifae.lean)
-/
@[path]
private lemma bc89_upperLines_genuineTcount_zero_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  bc89_genuineTcount bc60_upperLines n = 0 := by
-- proof
  apply StatMech.Walls.bc89_upperLines_genuineTcount_zero n

/--
[bc89_upperLines_genuine_le_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc89genuinetrifae.lean)
-/
@[path]
private lemma bc89_upperLines_genuine_le_boundary_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  bc89_genuineTcount bc60_upperLines n ≤ boxSV_boundaryCard 2 n := by
-- proof
  apply StatMech.Walls.bc89_upperLines_genuine_le_boundary n

/--
[bc89_genuineTcount_le_boundary_of_openForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc89genuinetrifae.lean)
-/
@[path]
private lemma bc89_genuineTcount_le_boundary_of_openForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bst_BoxOpenForest ω n) :
-- imply
  bc89_genuineTcount ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc89_genuineTcount_le_boundary_of_openForest ω n h

/--
[bc89_coarse_target_faithful](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc89genuinetrifae.lean)
-/
@[path]
private lemma bc89_coarse_target_faithful_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) := by
-- proof
  apply StatMech.Walls.bc89_coarse_target_faithful hL

/--
[bc89_audit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc89genuinetrifae.lean)
-/
@[path]
private lemma bc89_audit_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
-- imply
  (∃ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1) ∧ (∀ R : ℕ, ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0} = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ) ∧ ((∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) → bc61_CoarseTrifExistence μ L → μ {ω | numInfiniteClusters d ω = ⊤} = 0) ∧ ((∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) → bc61_CoarseTrifExistence μ L → (∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters d ω = k} = 1 → ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k)) → μ {ω | numInfiniteClusters d ω ≤ 1} = 1) := by
-- proof
  apply StatMech.Walls.bc89_audit μ hd L herg hfe hinv

/--
[bc89_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc89genuinetrifae.lean)
-/
@[path]
private lemma bc89_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2), bc89_GenuineTrif 2 ω x → IsTrifurcation 2 ω x) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), bc89_genuineTcount ω n ≤ Tcount 2 ω n) ∧ (∀ x : Site 2, ¬ bc89_GenuineTrif 2 bc60_upperLines x) ∧ (∀ n : ℕ, bc89_genuineTcount bc60_upperLines n = 0) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2), bc89_GenuineTrif 2 ω x → ∃ a₁ a₂ a₃ : Site 2, (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧ (openSubgraph 2 ω).Adj x a₁ ∧ (openSubgraph 2 ω).Adj x a₂ ∧ (openSubgraph 2 ω).Adj x a₃) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), bst_BoxOpenForest ω n → bc89_genuineTcount ω n ≤ boxSV_boundaryCard 2 n) ∧ (∀ {L : ℕ}, 3 ≤ L → bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2)) := by
-- proof
  apply StatMech.Walls.bc89_status


-- created on 2026-10-23
