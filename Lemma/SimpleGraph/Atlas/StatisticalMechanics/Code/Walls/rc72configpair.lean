import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc72configpair
open Finset StatMech StatMech.Walls


/--
[graftSwap_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc72configpair.lean)
-/
@[path]
private lemma graftSwap_involutive_eq
  {n : ℕ}
  {L : Finset (Fin n)} :
-- imply
  Function.Involutive (graftSwap L) := by
-- proof
  apply StatMech.Walls.graftSwap_involutive L

/--
[graftSwap_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc72configpair.lean)
-/
@[path]
private lemma graftSwap_bijective_eq
  {n : ℕ}
  {L : Finset (Fin n)} :
-- imply
  Function.Bijective (graftSwap L) := by
-- proof
  apply StatMech.Walls.graftSwap_bijective L

/--
[graftSwap_fst_off](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc72configpair.lean)
-/
@[path]
private lemma graftSwap_fst_off_eq
  {n : ℕ}
  {L : Finset (Fin n)}
  {p : ConfigSpace (Fin n) × ConfigSpace (Fin n)}
  {i : Fin n}
-- given
  (hi : i ∉ L) :
-- imply
  (graftSwap L p).1 i = p.1 i := by
-- proof
  apply StatMech.Walls.graftSwap_fst_off L p hi

/--
[graftSwap_snd_on](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc72configpair.lean)
-/
@[path]
private lemma graftSwap_snd_on_eq
  {n : ℕ}
  {L : Finset (Fin n)}
  {p : ConfigSpace (Fin n) × ConfigSpace (Fin n)}
  {i : Fin n}
-- given
  (hi : i ∈ L) :
-- imply
  (graftSwap L p).2 i = p.1 i := by
-- proof
  apply StatMech.Walls.graftSwap_snd_on L p hi

/--
[graftSwap_mapsInto_of_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc72configpair.lean)
-/
@[path]
private lemma graftSwap_mapsInto_of_witness_eq
  {n : ℕ}
  {A B : Set (ConfigSpace (Fin n))}
  {K L : Finset (Fin n)}
  {ω₁ ω₂ : ConfigSpace (Fin n)}
-- given
  (hKL : Disjoint K L)
  (hA : OccursOn A (K : Set (Fin n)) ω₁)
  (hB : OccursOn B (L : Set (Fin n)) ω₁) :
-- imply
  (graftSwap L (ω₁, ω₂)).1 ∈ A ∧ (graftSwap L (ω₁, ω₂)).2 ∈ B := by
-- proof
  apply StatMech.Walls.graftSwap_mapsInto_of_witness A B hKL ω₁ ω₂ hA hB

/--
[graftSwap_pair_perm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc72configpair.lean)
-/
@[path]
private lemma graftSwap_pair_perm_eq
  {n : ℕ}
  {L : Finset (Fin n)}
  {p : ConfigSpace (Fin n) × ConfigSpace (Fin n)}
  {i : Fin n} :
-- imply
  ((graftSwap L p).1 i, (graftSwap L p).2 i) = (p.1 i, p.2 i) ∨ ((graftSwap L p).1 i, (graftSwap L p).2 i) = (p.2 i, p.1 i) := by
-- proof
  apply StatMech.Walls.graftSwap_pair_perm L p i

/--
[graftSwap_jointCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc72configpair.lean)
-/
@[path]
private lemma graftSwap_jointCount_eq
  {n : ℕ}
  {L : Finset (Fin n)}
  {p : ConfigSpace (Fin n) × ConfigSpace (Fin n)} :
-- imply
  (Finset.univ.filter (fun i => (graftSwap L p).1 i = true)).card + (Finset.univ.filter (fun i => (graftSwap L p).2 i = true)).card = (Finset.univ.filter (fun i => p.1 i = true)).card + (Finset.univ.filter (fun i => p.2 i = true)).card := by
-- proof
  apply StatMech.Walls.graftSwap_jointCount L p

/--
[rc72_witness_counts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc72configpair.lean)
-/
@[path]
private lemma rc72_witness_counts_eq
  {n : ℕ} :
-- imply
  (rc72_disjOcc rc72_wA rc72_wB).card = 2 ∧ rc72_wA.card * rc72_wB.card = 9 ∧ (rc72_reachCells rc72_wA rc72_wB).card = 7 := by
-- proof
  apply StatMech.Walls.rc72_witness_counts

/--
[rc72_graftSwap_reach_cap_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc72configpair.lean)
-/
@[path]
private lemma rc72_graftSwap_reach_cap_fin2_eq
  {n : ℕ} :
-- imply
  (rc72_reachCells rc72_wA rc72_wB).card < 2 ^ 2 * (rc72_disjOcc rc72_wA rc72_wB).card := by
-- proof
  apply StatMech.Walls.rc72_graftSwap_reach_cap_fin2

/--
[rc72_source_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc72configpair.lean)
-/
@[path]
private lemma rc72_source_card_eq
  {n : ℕ}
  {A B : Finset (ConfigSpace (Fin 2))} :
-- imply
  (rc72_source A B).card = (rc72_disjOcc A B).card * 2 ^ 2 := by
-- proof
  apply StatMech.Walls.rc72_source_card A B

/--
[rc72_graftSwap_mem_reachCells](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc72configpair.lean)
-/
@[path]
private lemma rc72_graftSwap_mem_reachCells_eq
  {n : ℕ}
  {A B : Finset (ConfigSpace (Fin 2))}
  {ω₁ ω₂ : ConfigSpace (Fin 2)}
  {L : Finset (Fin 2)}
-- given
  (hω₁ : ω₁ ∈ rc72_disjOcc A B)
  (hL : L ∈ rc72_wits A B ω₁)
  (hAB : (graftSwap L (ω₁, ω₂)).1 ∈ A ∧ (graftSwap L (ω₁, ω₂)).2 ∈ B) :
-- imply
  graftSwap L (ω₁, ω₂) ∈ rc72_reachCells A B := by
-- proof
  apply StatMech.Walls.rc72_graftSwap_mem_reachCells A B hω₁ hL hAB

/--
[rc72_source_card_le_reach_of_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc72configpair.lean)
-/
@[path]
private lemma rc72_source_card_le_reach_of_injection_eq
  {n : ℕ}
  {A B : Finset (ConfigSpace (Fin 2))}
  {Lc : ConfigSpace (Fin 2) → ConfigSpace (Fin 2) → Finset (Fin 2)}
-- given
  (hwit : ∀ ω₁ ∈ rc72_disjOcc A B, ∀ ω₂ : ConfigSpace (Fin 2), Lc ω₁ ω₂ ∈ rc72_wits A B ω₁)
  (hAB : ∀ ω₁ ∈ rc72_disjOcc A B, ∀ ω₂ : ConfigSpace (Fin 2), (graftSwap (Lc ω₁ ω₂) (ω₁, ω₂)).1 ∈ A ∧ (graftSwap (Lc ω₁ ω₂) (ω₁, ω₂)).2 ∈ B)
  (hinj : Set.InjOn (fun p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) => graftSwap (Lc p.1 p.2) p) (rc72_source A B)) :
-- imply
  2 ^ 2 * (rc72_disjOcc A B).card ≤ (rc72_reachCells A B).card := by
-- proof
  apply StatMech.Walls.rc72_source_card_le_reach_of_injection A B Lc hwit hAB hinj

/--
[rc72_no_graftSwap_injection_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc72configpair.lean)
-/
@[path]
private lemma rc72_no_graftSwap_injection_fin2_eq
  {n : ℕ} :
-- imply
  ¬ ∃ Lc : ConfigSpace (Fin 2) → ConfigSpace (Fin 2) → Finset (Fin 2), (∀ ω₁ ∈ rc72_disjOcc rc72_wA rc72_wB, ∀ ω₂ : ConfigSpace (Fin 2), Lc ω₁ ω₂ ∈ rc72_wits rc72_wA rc72_wB ω₁) ∧ (∀ ω₁ ∈ rc72_disjOcc rc72_wA rc72_wB, ∀ ω₂ : ConfigSpace (Fin 2), (graftSwap (Lc ω₁ ω₂) (ω₁, ω₂)).1 ∈ rc72_wA ∧ (graftSwap (Lc ω₁ ω₂) (ω₁, ω₂)).2 ∈ rc72_wB) ∧ Set.InjOn (fun p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) => graftSwap (Lc p.1 p.2) p) (rc72_source rc72_wA rc72_wB) := by
-- proof
  apply StatMech.Walls.rc72_no_graftSwap_injection_fin2

/--
[rc72_reimerWprobCore_of_boxUnionBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc72configpair.lean)
-/
@[path]
private lemma rc72_reimerWprobCore_of_boxUnionBound_eq
  {n : ℕ}
-- given
  (h : rc60_BoxUnionBound) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc72_reimerWprobCore_of_boxUnionBound h

/--
[rc72_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc72configpair.lean)
-/
@[path]
private lemma rc72_status_eq
  {n : ℕ} :
-- imply
  (∀ (m : ℕ) (L : Finset (Fin m)), Function.Bijective (graftSwap L)) ∧ (∀ (m : ℕ) (L : Finset (Fin m)) (p : ConfigSpace (Fin m) × ConfigSpace (Fin m)), (Finset.univ.filter (fun i => (graftSwap L p).1 i = true)).card + (Finset.univ.filter (fun i => (graftSwap L p).2 i = true)).card = (Finset.univ.filter (fun i => p.1 i = true)).card + (Finset.univ.filter (fun i => p.2 i = true)).card) ∧ (∀ (m : ℕ) (A B : Set (ConfigSpace (Fin m))) (K L : Finset (Fin m)), Disjoint K L → ∀ (ω₁ ω₂ : ConfigSpace (Fin m)), OccursOn A (K : Set (Fin m)) ω₁ → OccursOn B (L : Set (Fin m)) ω₁ → (graftSwap L (ω₁, ω₂)).1 ∈ A ∧ (graftSwap L (ω₁, ω₂)).2 ∈ B) ∧ ((rc72_reachCells rc72_wA rc72_wB).card < 2 ^ 2 * (rc72_disjOcc rc72_wA rc72_wB).card) ∧ (¬ ∃ Lc : ConfigSpace (Fin 2) → ConfigSpace (Fin 2) → Finset (Fin 2), (∀ ω₁ ∈ rc72_disjOcc rc72_wA rc72_wB, ∀ ω₂ : ConfigSpace (Fin 2), Lc ω₁ ω₂ ∈ rc72_wits rc72_wA rc72_wB ω₁) ∧ (∀ ω₁ ∈ rc72_disjOcc rc72_wA rc72_wB, ∀ ω₂ : ConfigSpace (Fin 2), (graftSwap (Lc ω₁ ω₂) (ω₁, ω₂)).1 ∈ rc72_wA ∧ (graftSwap (Lc ω₁ ω₂) (ω₁, ω₂)).2 ∈ rc72_wB) ∧ Set.InjOn (fun p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) => graftSwap (Lc p.1 p.2) p) (rc72_source rc72_wA rc72_wB)) ∧ (rc60_BoxUnionBound → ReimerWprobCore) := by
-- proof
  apply StatMech.Walls.rc72_status


-- created on 2026-10-23
