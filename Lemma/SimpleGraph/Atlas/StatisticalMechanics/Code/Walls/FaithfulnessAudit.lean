import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.FaithfulnessAudit.Part2
open Finset SimpleGraph StatMech StatMech.Ising StatMech.Walls.GhcEqGap StatMech.Lattice StatMech.Percolation StatMech.Walls


/--
[fa_spin_flipAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean)
-/
@[path]
private lemma fa_spin_flipAll_eq
  {s : ConfigSpace V}
  {x : V} :
-- imply
  spin (fa_flipAll s) x = - spin s x := by
-- proof
  apply StatMech.Walls.fa_spin_flipAll s x

/--
[fa_flipAll_bij](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean)
-/
@[path]
private lemma fa_flipAll_bij_eq :
-- imply
  Function.Bijective (fa_flipAll (V := V)) := by
-- proof
  apply StatMech.Walls.fa_flipAll_bij

/--
[fa_bond_flipAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean)
-/
@[path]
private lemma fa_bond_flipAll_eq
  {s : ConfigSpace V}
  {e : Sym2 V} :
-- imply
  bond (fa_flipAll s) e = bond s e := by
-- proof
  apply StatMech.Walls.fa_bond_flipAll s e

/--
[fa_weight_flipAll_h0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean)
-/
@[path]
private lemma fa_weight_flipAll_h0_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {s : ConfigSpace V} :
-- imply
  isingWeight G β 0 (fa_flipAll s) = isingWeight G β 0 s := by
-- proof
  apply StatMech.Walls.fa_weight_flipAll_h0 G β s

/--
[fa_prob_flipAll_h0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean)
-/
@[path]
private lemma fa_prob_flipAll_h0_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {s : ConfigSpace V} :
-- imply
  isingProb G β 0 (fa_flipAll s) = isingProb G β 0 s := by
-- proof
  apply StatMech.Walls.fa_prob_flipAll_h0 G β s

/--
[fa_exp_odd_vanish_h0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean)
-/
@[path]
private lemma fa_exp_odd_vanish_h0_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {f : ConfigSpace V → ℝ}
-- given
  (hodd : ∀ s, f (fa_flipAll s) = - f s) :
-- imply
  isingExpectation G β 0 f = 0 := by
-- proof
  apply StatMech.Walls.fa_exp_odd_vanish_h0 G β f hodd

/--
[fa_ghs_ursell3_h0_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean)
-/
@[path]
private lemma fa_ghs_ursell3_h0_eq_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o x y : V} :
-- imply
  eg_ursell3 G β 0 o x y = 0 := by
-- proof
  apply StatMech.Walls.fa_ghs_ursell3_h0_eq_zero G β o x y

/--
[fa_ghs_ursell3_h0_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean)
-/
@[path]
private lemma fa_ghs_ursell3_h0_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o x y : V} :
-- imply
  eg_ursell3 G β 0 o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.fa_ghs_ursell3_h0_nonpos G β o x y

/--
[fa_ghs_ursell3_degenerate_formula](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean)
-/
@[path]
private lemma fa_ghs_ursell3_degenerate_formula_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {v : V}
-- given
  (β h : ℝ) :
-- imply
  eg_ursell3 G β h v v v = 2 * (isingExpectation G β h (fun s => spin s v))^3 - 2 * isingExpectation G β h (fun s => spin s v) := by
-- proof
  apply StatMech.Walls.fa_ghs_ursell3_degenerate_formula G β h v

/--
[fa_ghs_ursell3_degenerate_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean)
-/
@[path]
private lemma fa_ghs_ursell3_degenerate_neg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {v : V}
-- given
  (β h : ℝ)
  (hpos : 0 < isingExpectation G β h (fun s => spin s v))
  (hlt : isingExpectation G β h (fun s => spin s v) < 1) :
-- imply
  eg_ursell3 G β h v v v < 0 := by
-- proof
  apply StatMech.Walls.fa_ghs_ursell3_degenerate_neg G β h v hpos hlt

/--
[fa_ghs_witness_masses_both_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean)
-/
@[path]
private lemma fa_ghs_witness_masses_both_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  hnw_mass hmu_TriG 1 (fun _ => 1) hmu_triM ({0} : Finset (Fin 3)) = 0 ∧ hnw_mass hmu_TriG 1 (fun _ => 1) gc31_zeroM ({0} : Finset (Fin 3)) = 0 := by
-- proof
  apply StatMech.Walls.fa_ghs_witness_masses_both_zero G

/--
[fa_ghs_witness_doubling_is_trivial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean)
-/
@[path]
private lemma fa_ghs_witness_doubling_is_trivial_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  2 * hnw_mass hmu_TriG 1 (fun _ => 1) hmu_triM ({0} : Finset (Fin 3)) = hnw_mass hmu_TriG 1 (fun _ => 1) gc31_zeroM ({0} : Finset (Fin 3)) := by
-- proof
  apply StatMech.Walls.fa_ghs_witness_doubling_is_trivial G

/--
[fa_ghs_witness_sources_incompatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean)
-/
@[path]
private lemma fa_ghs_witness_sources_incompatible_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  Sharpness.sources hmu_TriG hmu_triM ≠ ({0} : Finset (Fin 3)) := by
-- proof
  apply StatMech.Walls.fa_ghs_witness_sources_incompatible G

/--
[fa_ghs_residue_binds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean)
-/
@[path]
private lemma fa_ghs_residue_binds_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ¬ gc31_MassDoublingSurgery hmu_TriG 1 (fun _ => 1) ({hmu_triM} : Finset (Sharpness.Current (Fin 3))) (∅ : Finset (Fin 3)) 0 1 2 := by
-- proof
  apply StatMech.Walls.fa_ghs_residue_binds G

/--
[fa_bk_boundary_pos_1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean)
-/
@[path]
private lemma fa_bk_boundary_pos_1_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ} :
-- imply
  0 < boxSV_boundaryCard 1 1 := by
-- proof
  apply StatMech.Walls.fa_bk_boundary_pos_1 G

/--
[fa_bk_boundary_pos_2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean)
-/
@[path]
private lemma fa_bk_boundary_pos_2_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ} :
-- imply
  0 < boxSV_boundaryCard 2 1 := by
-- proof
  apply StatMech.Walls.fa_bk_boundary_pos_2 G

/--
[fa_bk_Tcount_faithful](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean)
-/
@[path]
private lemma fa_bk_Tcount_faithful_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  Tcount d ω n = ((boxFinsetBK d n).filter (fun x => IsTrifurcation d ω x)).card := by
-- proof
  apply StatMech.Walls.fa_bk_Tcount_faithful G ω n

/--
[fa_bk_residue_entails_geometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean)
-/
@[path]
private lemma fa_bk_residue_entails_geometry_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ y₀ : Site d}
-- given
  (hx0box : x₀ ∈ box d n)
  (htx0 : IsTrifurcation d ω x₀)
  (hy0box : y₀ ∈ box d n)
  (hty0 : IsTrifurcation d ω y₀)
  (hxy : x₀ ≠ y₀)
  (hconn : Connected d ω x₀ y₀)
  (h : rfp_RootedArmDivergence ω n) :
-- imply
  (∃ b : Site d → Site d, ¬ fsp_sameArm ω y₀ (b x₀) (b y₀)) ∨ (∃ b : Site d → Site d, ¬ fsp_sameArm ω x₀ (b y₀) (b x₀)) := by
-- proof
  apply StatMech.Walls.fa_bk_residue_entails_geometry G ω n hx0box htx0 hy0box hty0 hxy hconn h

/--
[fa_bk_residue_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean)
-/
@[path]
private lemma fa_bk_residue_noTrif_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  rfp_RootedArmDivergence ω n := by
-- proof
  apply StatMech.Walls.fa_bk_residue_noTrif G ω n hno

/--
[fa_bk_residue_twoTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean)
-/
@[path]
private lemma fa_bk_residue_twoTrif_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ y₀ : Site d}
  {b : Site d → Site d}
-- given
  (hx0y0 : x₀ ≠ y₀)
  (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
  (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
  (hby0 : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
  (hdeep : ¬ fsp_sameArm ω y₀ (b x₀) (b y₀)) :
-- imply
  rfp_RootedArmDivergence ω n := by
-- proof
  apply StatMech.Walls.fa_bk_residue_twoTrif G ω n b hx0y0 htwo hbx0 hby0 hdeep

/--
[fa_bk_count_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean)
-/
@[path]
private lemma fa_bk_count_of_residue_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : rfp_RootedArmDivergence ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.fa_bk_count_of_residue G ω n hn h

/--
[fa_reimer_disjointOccurrence_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean)
-/
@[path]
private lemma fa_reimer_disjointOccurrence_subset_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {A B : Set (ConfigSpace E)} :
-- imply
  StatMech.disjointOccurrence A B ⊆ A ∩ B := by
-- proof
  apply StatMech.Walls.fa_reimer_disjointOccurrence_subset G A B

/--
[fa_reimer_target_true_fin1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean)
-/
@[path]
private lemma fa_reimer_target_true_fin1_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {φ : Fin 1 → Bool → ℝ}
  {A B : Set (ConfigSpace (Fin 1))}
-- given
  (hφ0 : ∀ i b, 0 ≤ φ i b)
  (hφ1 : ∀ i, φ i false + φ i true = 1) :
-- imply
  StatMech.wprob φ (StatMech.disjointOccurrence A B) ≤ StatMech.wprob φ A * StatMech.wprob φ B := by
-- proof
  apply StatMech.Walls.fa_reimer_target_true_fin1 G φ hφ0 hφ1 A B

/--
[fa_reimer_parA_not_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean)
-/
@[path]
private lemma fa_reimer_parA_not_increasing_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ} :
-- imply
  ¬ StatMech.IsIncreasing fa_reimer_parA := by
-- proof
  apply StatMech.Walls.fa_reimer_parA_not_increasing G

/--
[fa_reimer_target_true_nonmonotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean)
-/
@[path]
private lemma fa_reimer_target_true_nonmonotone_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {φ : Fin 4 → Bool → ℝ}
-- given
  (hφ1 : ∀ i, φ i false + φ i true = 1) :
-- imply
  StatMech.wprob φ (StatMech.disjointOccurrence fa_reimer_parA fa_reimer_parB) = StatMech.wprob φ fa_reimer_parA * StatMech.wprob φ fa_reimer_parB := by
-- proof
  apply StatMech.Walls.fa_reimer_target_true_nonmonotone G φ hφ1

/--
[fa_reimer_naive_familyBKR_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean)
-/
@[path]
private lemma fa_reimer_naive_familyBKR_false_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ} :
-- imply
  ¬ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))), #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) := by
-- proof
  apply StatMech.Walls.fa_reimer_naive_familyBKR_false G

/--
[fa_reimer_residue_iff_wall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean)
-/
@[path]
private lemma fa_reimer_residue_iff_wall_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ} :
-- imply
  rc18_CylBoxReflInter ↔ rc17_NonMonotoneDeficit := by
-- proof
  apply StatMech.Walls.fa_reimer_residue_iff_wall G

/--
[fa_reimer_residue_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean)
-/
@[path]
private lemma fa_reimer_residue_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ} :
-- imply
  ((¬ StatMech.IsIncreasing rbi_A ∧ ¬ StatMech.IsDecreasing rbi_A) ∨ (¬ StatMech.IsIncreasing rbi_B ∧ ¬ StatMech.IsDecreasing rbi_B)) ∧ #(rc18_cylBoxSupp rbi_A rbi_B) ≤ #(rc10_reflInter (eventFamily rbi_A) (eventFamily rbi_B)) := by
-- proof
  apply StatMech.Walls.fa_reimer_residue_nonvacuous G

/--
[fa_reimer_target_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean)
-/
@[path]
private lemma fa_reimer_target_of_residue_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
-- given
  (h : rc18_CylBoxReflInter) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.fa_reimer_target_of_residue G h


-- created on 2026-10-23
