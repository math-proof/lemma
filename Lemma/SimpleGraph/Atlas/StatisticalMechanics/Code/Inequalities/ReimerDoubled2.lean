import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled2
open Finset StatMech


/--
[uvCompress_singleton_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled2.lean)
-/
@[path]
private lemma uvCompress_singleton_empty_eq
  [DecidableEq α]
  {a : α}
  {s : Finset α} :
-- imply
  UV.compress ({a} : Finset α) ∅ s = insert a s := by
-- proof
  apply StatMech.uvCompress_singleton_empty a s

/--
[mem_upComp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled2.lean)
-/
@[path]
private lemma mem_upComp_eq
  [DecidableEq α]
  {a : α ⊕ α}
  {𝒜 : Finset (Finset (α ⊕ α))}
  {s : Finset (α ⊕ α)} :
-- imply
  s ∈ upComp a 𝒜 ↔ (s ∈ 𝒜 ∧ insert a s ∈ 𝒜) ∨ (s ∉ 𝒜 ∧ ∃ b ∈ 𝒜, insert a b = s) := by
-- proof
  apply StatMech.mem_upComp a 𝒜 s

/--
[mem_upRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled2.lean)
-/
@[path]
private lemma mem_upRight_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset (α ⊕ α))}
  {s : Finset (α ⊕ α)} :
-- imply
  s ∈ upRight i 𝒜 ↔ (s ∈ 𝒜 ∧ insert (Sum.inr i) s ∈ 𝒜) ∨ (s ∉ 𝒜 ∧ ∃ b ∈ 𝒜, insert (Sum.inr i) b = s) := by
-- proof
  apply StatMech.mem_upRight i 𝒜 s

/--
[mem_downLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled2.lean)
-/
@[path]
private lemma mem_downLeft_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset (α ⊕ α))}
  {s : Finset (α ⊕ α)} :
-- imply
  s ∈ downLeft i 𝒜 ↔ (s ∈ 𝒜 ∧ s.erase (Sum.inl i) ∈ 𝒜) ∨ (s ∉ 𝒜 ∧ insert (Sum.inl i) s ∈ 𝒜) := by
-- proof
  apply StatMech.mem_downLeft i 𝒜 s

/--
[insert_mem_upComp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled2.lean)
-/
@[path]
private lemma insert_mem_upComp_eq
  [DecidableEq α]
  {a : α ⊕ α}
  {𝒜 : Finset (Finset (α ⊕ α))}
  {b : Finset (α ⊕ α)}
-- given
  (hb : b ∈ 𝒜) :
-- imply
  insert a b ∈ upComp a 𝒜 := by
-- proof
  apply StatMech.insert_mem_upComp a 𝒜 hb

/--
[upComp_isUp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled2.lean)
-/
@[path]
private lemma upComp_isUp_eq
  [DecidableEq α]
  {a : α ⊕ α}
  {𝒜 : Finset (Finset (α ⊕ α))}
  {s : Finset (α ⊕ α)}
-- given
  (hs : s ∈ upComp a 𝒜) :
-- imply
  insert a s ∈ upComp a 𝒜 := by
-- proof
  apply StatMech.upComp_isUp a 𝒜 hs

/--
[downLeft_isDownAtLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled2.lean)
-/
@[path]
private lemma downLeft_isDownAtLeft_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset (α ⊕ α))} :
-- imply
  IsDownAtLeft i (downLeft i 𝒜) := by
-- proof
  apply StatMech.downLeft_isDownAtLeft i 𝒜

/--
[upRight_isUpAtRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled2.lean)
-/
@[path]
private lemma upRight_isUpAtRight_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset (α ⊕ α))} :
-- imply
  IsUpAtRight i (upRight i 𝒜) := by
-- proof
  apply StatMech.upRight_isUpAtRight i 𝒜

/--
[upRight_isDownAtLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled2.lean)
-/
@[path]
private lemma upRight_isDownAtLeft_eq
  [DecidableEq α]
  {i j : α}
  {𝒜 : Finset (Finset (α ⊕ α))}
-- given
  (h : IsDownAtLeft i 𝒜) :
-- imply
  IsDownAtLeft i (upRight j 𝒜) := by
-- proof
  apply StatMech.upRight_isDownAtLeft i j h

/--
[downLeft_isUpAtRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled2.lean)
-/
@[path]
private lemma downLeft_isUpAtRight_eq
  [DecidableEq α]
  {i j : α}
  {𝒜 : Finset (Finset (α ⊕ α))}
-- given
  (h : IsUpAtRight j 𝒜) :
-- imply
  IsUpAtRight j (downLeft i 𝒜) := by
-- proof
  apply StatMech.downLeft_isUpAtRight i j h

/--
[doubleCompress_isDownAtLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled2.lean)
-/
@[path]
private lemma doubleCompress_isDownAtLeft_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset (α ⊕ α))} :
-- imply
  IsDownAtLeft i (doubleCompress i 𝒜) := by
-- proof
  apply StatMech.doubleCompress_isDownAtLeft i 𝒜

/--
[doubleCompress_isUpAtRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled2.lean)
-/
@[path]
private lemma doubleCompress_isUpAtRight_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset (α ⊕ α))} :
-- imply
  IsUpAtRight i (doubleCompress i 𝒜) := by
-- proof
  apply StatMech.doubleCompress_isUpAtRight i 𝒜

/--
[doubleCompress_idem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled2.lean)
-/
@[path]
private lemma doubleCompress_idem_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset (α ⊕ α))} :
-- imply
  doubleCompress i (doubleCompress i 𝒜) = doubleCompress i 𝒜 := by
-- proof
  apply StatMech.doubleCompress_idem i 𝒜

/--
[boxDoubled_filter_notMem_inl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled2.lean)
-/
@[path]
private lemma boxDoubled_filter_notMem_inl_eq
  [DecidableEq α]
  {i : α}
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (boxDoubled 𝒜 ℬ).filter (fun U => Sum.inl i ∉ U) = boxDoubled (𝒜.filter (fun S => i ∉ S)) ℬ := by
-- proof
  apply StatMech.boxDoubled_filter_notMem_inl i 𝒜 ℬ

/--
[boxDoubled_filter_notMem_inr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled2.lean)
-/
@[path]
private lemma boxDoubled_filter_notMem_inr_eq
  [DecidableEq α]
  {i : α}
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (boxDoubled 𝒜 ℬ).filter (fun U => Sum.inr i ∉ U) = boxDoubled 𝒜 (ℬ.filter (fun T => i ∉ T)) := by
-- proof
  apply StatMech.boxDoubled_filter_notMem_inr i 𝒜 ℬ

/--
[boxDoubled_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled2.lean)
-/
@[path]
private lemma boxDoubled_mono_eq
  [DecidableEq α]
  {𝒜 𝒜' ℬ ℬ' : Finset (Finset α)}
-- given
  (h𝒜 : 𝒜 ⊆ 𝒜')
  (hℬ : ℬ ⊆ ℬ') :
-- imply
  boxDoubled 𝒜 ℬ ⊆ boxDoubled 𝒜' ℬ' := by
-- proof
  apply StatMech.boxDoubled_mono h𝒜 hℬ

/--
[card_boxDoubled_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled2.lean)
-/
@[path]
private lemma card_boxDoubled_mono_eq
  [DecidableEq α]
  {𝒜 𝒜' ℬ ℬ' : Finset (Finset α)}
-- given
  (h𝒜 : 𝒜 ⊆ 𝒜')
  (hℬ : ℬ ⊆ ℬ') :
-- imply
  (boxDoubled 𝒜 ℬ).card ≤ (boxDoubled 𝒜' ℬ').card := by
-- proof
  apply StatMech.card_boxDoubled_mono h𝒜 hℬ

/--
[dbl_parts_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled2.lean)
-/
@[path]
private lemma dbl_parts_disjoint_eq
  [DecidableEq α]
  {S T : Finset α} :
-- imply
  Disjoint (S.map ⟨Sum.inl, Sum.inl_injective⟩) (T.map ⟨Sum.inr, Sum.inr_injective⟩) := by
-- proof
  apply StatMech.dbl_parts_disjoint S T


-- created on 2026-10-23
