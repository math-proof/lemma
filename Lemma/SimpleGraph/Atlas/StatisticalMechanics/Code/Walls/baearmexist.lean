import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.baearmexist
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bae_neighbour_of_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/baearmexist.lean)
-/
@[path]
private lemma bae_neighbour_of_reach_eq
  {d : ℕ}
  [DecidableEq V]
  {T : SimpleGraph V}
  {x z : V}
-- given
  (hzx : z ≠ x)
  (hreach : T.Reachable x z) :
-- imply
  ∃ n, T.Adj x n ∧ ray34_AvoidReach T {x} n z := by
-- proof
  apply StatMech.Walls.bae_neighbour_of_reach T hzx hreach

/--
[bae_branch_lift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/baearmexist.lean)
-/
@[path]
private lemma bae_branch_lift_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {T : SimpleGraph (Site d)}
  {x n z : Site d}
-- given
  (hle : T ≤ openSubgraph d ω)
  (h : ray34_AvoidReach T {x} n z) :
-- imply
  (bkg_deleteVertex (openSubgraph d ω) x).Reachable n z := by
-- proof
  apply StatMech.Walls.bae_branch_lift T hle h

/--
[bae_cluster_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/baearmexist.lean)
-/
@[path]
private lemma bae_cluster_eq_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x a : Site d} :
-- imply
  cluster d (removeSites ({x} : Finset (Site d)) ω) a = ray34_AvoidCluster (bkg_deleteVertex (openSubgraph d ω) x) ∅ a := by
-- proof
  apply StatMech.Walls.bae_cluster_eq ω x a

/--
[bae_one_branch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/baearmexist.lean)
-/
@[path]
private lemma bae_one_branch_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {T : SimpleGraph (Site d)}
  [LocallyFinite T]
  {a : Site d}
-- given
  (hle : T ≤ openSubgraph d ω)
  (hspan : ∀ z, (openSubgraph d ω).Reachable x z → T.Reachable x z)
  (hxa : (openSubgraph d ω).Adj x a)
  (hinf : (ray34_AvoidCluster (bkg_deleteVertex (openSubgraph d ω) x) ∅ a).Infinite) :
-- imply
  ∃ n, T.Adj x n ∧ (ray34_AvoidCluster T {x} n).Infinite ∧ n ∈ ray34_AvoidCluster (bkg_deleteVertex (openSubgraph d ω) x) ∅ a := by
-- proof
  apply StatMech.Walls.bae_one_branch x T hle hspan hxa hinf

/--
[bae_three_infinite_branches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/baearmexist.lean)
-/
@[path]
private lemma bae_three_infinite_branches_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {T : SimpleGraph (Site d)}
  [LocallyFinite T]
-- given
  (hle : T ≤ openSubgraph d ω)
  (hspan : ∀ z, (openSubgraph d ω).Reachable x z → T.Reachable x z)
  (h : bft_FineTrif ω x) :
-- imply
  ∃ n₁ n₂ n₃ : Site d, (T.Adj x n₁ ∧ T.Adj x n₂ ∧ T.Adj x n₃) ∧ (n₁ ≠ n₂ ∧ n₁ ≠ n₃ ∧ n₂ ≠ n₃) ∧ ((ray34_AvoidCluster T {x} n₁).Infinite ∧ (ray34_AvoidCluster T {x} n₂).Infinite ∧ (ray34_AvoidCluster T {x} n₃).Infinite) := by
-- proof
  apply StatMech.Walls.bae_three_infinite_branches x T hle hspan h

/--
[bae_arm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/baearmexist.lean)
-/
@[path]
private lemma bae_arm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {T : SimpleGraph (Site d)}
  [LocallyFinite T]
  {n : Site d}
  {R : ℕ}
-- given
  (hle : T ≤ openSubgraph d ω)
  (hR : 1 ≤ R)
  (hadjxn : T.Adj x n)
  (hn : n ∈ box d R)
  (hbr : (ray34_AvoidCluster T {x} n).Infinite) :
-- imply
  ∃ (armRay : ℕ → Site d) (armLen : ℕ), armRay 0 = x ∧ armRay 1 = n ∧ 1 ≤ armLen ∧ (∀ k < armLen, T.Adj (armRay k) (armRay (k + 1))) ∧ Set.InjOn armRay {m | m ≤ armLen} ∧ armRay armLen ∈ vertexBoundary d R := by
-- proof
  apply StatMech.Walls.bae_arm x T hle hR hadjxn hn hbr

/--
[bae_trif_arms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/baearmexist.lean)
-/
@[path]
private lemma bae_trif_arms_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {T : SimpleGraph (Site d)}
  [LocallyFinite T]
  {R : ℕ}
-- given
  (hle : T ≤ openSubgraph d ω)
  (hspan : ∀ z, (openSubgraph d ω).Reachable x z → T.Reachable x z)
  (hR : 1 ≤ R)
  (hnbox : ∀ n, T.Adj x n → n ∈ box d R)
  (h : bft_FineTrif ω x) :
-- imply
  ∃ (ρ₁ ρ₂ ρ₃ : ℕ → Site d) (ℓ₁ ℓ₂ ℓ₃ : ℕ), (ρ₁ 0 = x ∧ ρ₂ 0 = x ∧ ρ₃ 0 = x) ∧ (ρ₁ 1 ≠ ρ₂ 1 ∧ ρ₁ 1 ≠ ρ₃ 1 ∧ ρ₂ 1 ≠ ρ₃ 1) ∧ (1 ≤ ℓ₁ ∧ 1 ≤ ℓ₂ ∧ 1 ≤ ℓ₃) ∧ ((∀ k < ℓ₁, T.Adj (ρ₁ k) (ρ₁ (k + 1))) ∧ (∀ k < ℓ₂, T.Adj (ρ₂ k) (ρ₂ (k + 1))) ∧ (∀ k < ℓ₃, T.Adj (ρ₃ k) (ρ₃ (k + 1)))) ∧ (Set.InjOn ρ₁ {m | m ≤ ℓ₁} ∧ Set.InjOn ρ₂ {m | m ≤ ℓ₂} ∧ Set.InjOn ρ₃ {m | m ≤ ℓ₃}) ∧ (ρ₁ ℓ₁ ∈ vertexBoundary d R ∧ ρ₂ ℓ₂ ∈ vertexBoundary d R ∧ ρ₃ ℓ₃ ∈ vertexBoundary d R) := by
-- proof
  apply StatMech.Walls.bae_trif_arms x T hle hspan hR hnbox h

/--
[bae_fineTrifs_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/baearmexist.lean)
-/
@[path]
private lemma bae_fineTrifs_finite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {R : ℕ} :
-- imply
  {x : Site d | x ∈ box d R ∧ bft_FineTrif ω x}.Finite := by
-- proof
  apply StatMech.Walls.bae_fineTrifs_finite ω R

/--
[bae_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/baearmexist.lean)
-/
@[path]
private lemma bae_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2) (T : SimpleGraph (Site 2)) [_i : LocallyFinite T], T ≤ openSubgraph 2 ω → (∀ z, (openSubgraph 2 ω).Reachable x z → T.Reachable x z) → bft_FineTrif ω x → ∃ n₁ n₂ n₃ : Site 2, (T.Adj x n₁ ∧ T.Adj x n₂ ∧ T.Adj x n₃) ∧ (n₁ ≠ n₂ ∧ n₁ ≠ n₃ ∧ n₂ ≠ n₃) ∧ ((ray34_AvoidCluster T {x} n₁).Infinite ∧ (ray34_AvoidCluster T {x} n₂).Infinite ∧ (ray34_AvoidCluster T {x} n₃).Infinite)) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2) (T : SimpleGraph (Site 2)) [_i : LocallyFinite T], T ≤ openSubgraph 2 ω → ∀ {n : Site 2} {R : ℕ}, 1 ≤ R → T.Adj x n → n ∈ box 2 R → (ray34_AvoidCluster T {x} n).Infinite → ∃ (armRay : ℕ → Site 2) (armLen : ℕ), armRay 0 = x ∧ armRay 1 = n ∧ 1 ≤ armLen ∧ (∀ k < armLen, T.Adj (armRay k) (armRay (k + 1))) ∧ Set.InjOn armRay {m | m ≤ armLen} ∧ armRay armLen ∈ vertexBoundary 2 R) ∧ (Fintype.card (Fin 1) ≤ ({1, 2, 3} : Finset (Fin 4)).card) := by
-- proof
  apply StatMech.Walls.bae_status


-- created on 2026-10-23
