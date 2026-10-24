import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.BeffaraDC.AnimalLLN
open StatMech StatMech.BeffaraDC


/--
[mem_animalsLE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLN.lean)
-/
@[path]
private lemma mem_animalsLE_eq
  [DecidableEq V]
  [Fintype V]
  {o : V}
  {n : ℕ}
  {S : Finset V} :
-- imply
  S ∈ animalsLE o n ↔ o ∈ S ∧ S.card ≤ n := by
-- proof
  apply StatMech.BeffaraDC.mem_animalsLE

/--
[animalsLE_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLN.lean)
-/
@[path]
private lemma animalsLE_nonempty_eq
  [DecidableEq V]
  [Fintype V]
  {o : V}
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  (animalsLE o n).Nonempty := by
-- proof
  apply StatMech.BeffaraDC.animalsLE_nonempty o hn

/--
[animalsLE_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLN.lean)
-/
@[path]
private lemma animalsLE_mono_eq
  [DecidableEq V]
  [Fintype V]
  {o : V}
  {m n : ℕ}
-- given
  (h : m ≤ n) :
-- imply
  animalsLE o m ⊆ animalsLE o n := by
-- proof
  apply StatMech.BeffaraDC.animalsLE_mono o h

/--
[greedyAnimalValue_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLN.lean)
-/
@[path]
private lemma greedyAnimalValue_eq_sum_eq
  [DecidableEq V]
  [Fintype V]
  {w : V → ℝ}
  {o : V}
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  ∃ S ∈ animalsLE o n, greedyAnimalValue w o n = ∑ v ∈ S, w v := by
-- proof
  apply StatMech.BeffaraDC.greedyAnimalValue_eq_sum w o hn

/--
[greedyAnimalValue_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLN.lean)
-/
@[path]
private lemma greedyAnimalValue_nonneg_eq
  [DecidableEq V]
  [Fintype V]
  {w : V → ℝ}
  {o : V}
  {n : ℕ}
-- given
  (hw : ∀ v, 0 ≤ w v) :
-- imply
  0 ≤ greedyAnimalValue w o n := by
-- proof
  apply StatMech.BeffaraDC.greedyAnimalValue_nonneg hw o n

/--
[greedyAnimalValue_ge_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLN.lean)
-/
@[path]
private lemma greedyAnimalValue_ge_root_eq
  [DecidableEq V]
  [Fintype V]
  {w : V → ℝ}
  {o : V}
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  w o ≤ greedyAnimalValue w o n := by
-- proof
  apply StatMech.BeffaraDC.greedyAnimalValue_ge_root o hn

/--
[greedyAnimalValue_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLN.lean)
-/
@[path]
private lemma greedyAnimalValue_mono_eq
  [DecidableEq V]
  [Fintype V]
  {w : V → ℝ}
  {o : V}
  {m n : ℕ}
-- given
  (hw : ∀ v, 0 ≤ w v)
  (hmn : m ≤ n) :
-- imply
  greedyAnimalValue w o m ≤ greedyAnimalValue w o n := by
-- proof
  apply StatMech.BeffaraDC.greedyAnimalValue_mono hw o hmn

/--
[greedyAnimalValue_le_card_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLN.lean)
-/
@[path]
private lemma greedyAnimalValue_le_card_mul_eq
  [DecidableEq V]
  [Fintype V]
  {w : V → ℝ}
  {M : ℝ}
  {o : V}
  {n : ℕ}
-- given
  (hM : ∀ v, w v ≤ M)
  (hM0 : 0 ≤ M) :
-- imply
  greedyAnimalValue w o n ≤ M * n := by
-- proof
  apply StatMech.BeffaraDC.greedyAnimalValue_le_card_mul hM hM0 o n

/--
[greedyAnimalValue_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLN.lean)
-/
@[path]
private lemma greedyAnimalValue_split_eq
  [DecidableEq V]
  [Fintype V]
  {w : V → ℝ}
  {o : V}
  {m n : ℕ}
  {S : Finset V}
-- given
  (hw : ∀ v, 0 ≤ w v)
  (hoS : o ∈ S)
  (hcard : S.card ≤ m + n + 1) :
-- imply
  ∑ v ∈ S, w v ≤ greedyAnimalValue w o (m + 1) + greedyAnimalValue w o (n + 1) := by
-- proof
  apply StatMech.BeffaraDC.greedyAnimalValue_split hw o m n hoS hcard

/--
[greedyAnimalValue_succ_subadditive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLN.lean)
-/
@[path]
private lemma greedyAnimalValue_succ_subadditive_eq
  [DecidableEq V]
  [Fintype V]
  {w : V → ℝ}
  {o : V}
-- given
  (hw : ∀ v, 0 ≤ w v) :
-- imply
  Subadditive (fun n => greedyAnimalValue w o (n + 1)) := by
-- proof
  apply StatMech.BeffaraDC.greedyAnimalValue_succ_subadditive hw o

/--
[greedyAnimalValue_bddBelow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLN.lean)
-/
@[path]
private lemma greedyAnimalValue_bddBelow_eq
  [DecidableEq V]
  [Fintype V]
  {w : V → ℝ}
  {o : V}
-- given
  (hw : ∀ v, 0 ≤ w v) :
-- imply
  BddBelow (Set.range fun n => greedyAnimalValue w o (n + 1) / n) := by
-- proof
  apply StatMech.BeffaraDC.greedyAnimalValue_bddBelow hw o

/--
[greedyAnimalValue_lln](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLN.lean)
-/
@[path]
private lemma greedyAnimalValue_lln_eq
  [DecidableEq V]
  [Fintype V]
  {w : V → ℝ}
  {o : V}
-- given
  (hw : ∀ v, 0 ≤ w v) :
-- imply
  Tendsto (fun n => greedyAnimalValue w o (n + 1) / n) atTop (𝓝 (greedyAnimalValue_succ_subadditive hw o).lim) := by
-- proof
  apply StatMech.BeffaraDC.greedyAnimalValue_lln hw o

/--
[greedyAnimalValue_lln_eq_iInf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLN.lean)
-/
@[path]
private lemma greedyAnimalValue_lln_eq_iInf_eq
  [DecidableEq V]
  [Fintype V]
  {w : V → ℝ}
  {o : V}
-- given
  (hw : ∀ v, 0 ≤ w v) :
-- imply
  (greedyAnimalValue_succ_subadditive hw o).lim = sInf ((fun n : ℕ => greedyAnimalValue w o (n + 1) / n) '' Set.Ici 1) := by
-- proof
  apply StatMech.BeffaraDC.greedyAnimalValue_lln_eq_iInf hw o

/--
[greedyAnimalValue_lln_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLN.lean)
-/
@[path]
private lemma greedyAnimalValue_lln_le_eq
  [DecidableEq V]
  [Fintype V]
  {w : V → ℝ}
  {o : V}
  {n : ℕ}
-- given
  (hw : ∀ v, 0 ≤ w v)
  (hn : n ≠ 0) :
-- imply
  (greedyAnimalValue_succ_subadditive hw o).lim ≤ greedyAnimalValue w o (n + 1) / n := by
-- proof
  apply StatMech.BeffaraDC.greedyAnimalValue_lln_le hw o hn

/--
[greedyAnimalValue_lln_le_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLN.lean)
-/
@[path]
private lemma greedyAnimalValue_lln_le_bound_eq
  [DecidableEq V]
  [Fintype V]
  {w : V → ℝ}
  {M : ℝ}
  {o : V}
-- given
  (hw : ∀ v, 0 ≤ w v)
  (hM : ∀ v, w v ≤ M)
  (hM0 : 0 ≤ M) :
-- imply
  (greedyAnimalValue_succ_subadditive hw o).lim ≤ M := by
-- proof
  apply StatMech.BeffaraDC.greedyAnimalValue_lln_le_bound hw hM hM0 o

/--
[subGreedyAnimalValue_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLN.lean)
-/
@[path]
private lemma subGreedyAnimalValue_le_eq
  [DecidableEq V]
  [Fintype V]
  {𝒜 : ℕ → Finset (Finset V)}
  {w : V → ℝ}
  {o : V}
  {n : ℕ}
-- given
  (hw : ∀ v, 0 ≤ w v)
  (hsub : ∀ n, 𝒜 n ⊆ animalsLE o n) :
-- imply
  subGreedyAnimalValue 𝒜 w n ≤ greedyAnimalValue w o n := by
-- proof
  apply StatMech.BeffaraDC.subGreedyAnimalValue_le hw o hsub n

/--
[subGreedyAnimalValue_le_card_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLN.lean)
-/
@[path]
private lemma subGreedyAnimalValue_le_card_mul_eq
  [DecidableEq V]
  [Fintype V]
  {𝒜 : ℕ → Finset (Finset V)}
  {w : V → ℝ}
  {M : ℝ}
  {o : V}
  {n : ℕ}
-- given
  (hw : ∀ v, 0 ≤ w v)
  (hM : ∀ v, w v ≤ M)
  (hM0 : 0 ≤ M)
  (hsub : ∀ n, 𝒜 n ⊆ animalsLE o n) :
-- imply
  subGreedyAnimalValue 𝒜 w n ≤ M * n := by
-- proof
  apply StatMech.BeffaraDC.subGreedyAnimalValue_le_card_mul hw hM hM0 o hsub n


-- created on 2026-10-23
