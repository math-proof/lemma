import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Inequalities.ReimerCompressionClose
open Finset StatMech


/--
[fwt_insert_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressionClose.lean)
-/
@[path]
private lemma fwt_insert_mul_eq
  [Fintype α]
  [DecidableEq α]
  {w : α → Bool → ℝ}
  {t : Finset α}
  {a : α}
-- given
  (ha : a ∉ t) :
-- imply
  fwt w (insert a t) * w a false = fwt w t * w a true := by
-- proof
  apply StatMech.fwt_insert_mul w ha

/--
[fwt_le_erase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressionClose.lean)
-/
@[path]
private lemma fwt_le_erase_eq
  [Fintype α]
  [DecidableEq α]
  {w : α → Bool → ℝ}
  {a : α}
  {s : Finset α}
-- given
  (hw0 : ∀ x b, 0 ≤ w x b)
  (hdom : w a true ≤ w a false)
  (ha : a ∈ s) :
-- imply
  fwt w s ≤ fwt w (s.erase a) := by
-- proof
  apply StatMech.fwt_le_erase hw0 hdom ha

/--
[fwt_le_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressionClose.lean)
-/
@[path]
private lemma fwt_le_insert_eq
  [Fintype α]
  [DecidableEq α]
  {w : α → Bool → ℝ}
  {a : α}
  {s : Finset α}
-- given
  (hw0 : ∀ x b, 0 ≤ w x b)
  (hdom : w a false ≤ w a true)
  (ha : a ∉ s) :
-- imply
  fwt w s ≤ fwt w (insert a s) := by
-- proof
  apply StatMech.fwt_le_insert hw0 hdom ha

/--
[mem_of_erase_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressionClose.lean)
-/
@[path]
private lemma mem_of_erase_notMem_eq
  [Fintype α]
  [DecidableEq α]
  {a : α}
  {𝒜 : Finset (Finset α)}
  {s : Finset α}
-- given
  (hs : s ∈ 𝒜)
  (h : s.erase a ∉ 𝒜) :
-- imply
  a ∈ s := by
-- proof
  apply StatMech.mem_of_erase_notMem hs h

/--
[fmarg_le_downCompression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressionClose.lean)
-/
@[path]
private lemma fmarg_le_downCompression_eq
  [Fintype α]
  [DecidableEq α]
  {w : α → Bool → ℝ}
  {a : α}
  {𝒜 : Finset (Finset α)}
-- given
  (hw0 : ∀ x b, 0 ≤ w x b)
  (hdom : w a true ≤ w a false) :
-- imply
  fmarg w 𝒜 ≤ fmarg w (Down.compression a 𝒜) := by
-- proof
  apply StatMech.fmarg_le_downCompression hw0 a hdom 𝒜

/--
[compress_singleton_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressionClose.lean)
-/
@[path]
private lemma compress_singleton_empty_eq
  [Fintype α]
  [DecidableEq α]
  {a : α}
  {s : Finset α} :
-- imply
  UV.compress ({a} : Finset α) ∅ s = if a ∈ s then s else insert a s := by
-- proof
  apply StatMech.compress_singleton_empty a s

/--
[notMem_of_compress_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressionClose.lean)
-/
@[path]
private lemma notMem_of_compress_notMem_eq
  [Fintype α]
  [DecidableEq α]
  {a : α}
  {𝒜 : Finset (Finset α)}
  {s : Finset α}
-- given
  (hs : s ∈ 𝒜)
  (h : UV.compress ({a} : Finset α) ∅ s ∉ 𝒜) :
-- imply
  a ∉ s := by
-- proof
  apply StatMech.notMem_of_compress_notMem hs h

/--
[fmarg_le_upCompression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressionClose.lean)
-/
@[path]
private lemma fmarg_le_upCompression_eq
  [Fintype α]
  [DecidableEq α]
  {w : α → Bool → ℝ}
  {a : α}
  {𝒜 : Finset (Finset α)}
-- given
  (hw0 : ∀ x b, 0 ≤ w x b)
  (hdom : w a false ≤ w a true) :
-- imply
  fmarg w 𝒜 ≤ fmarg w (UV.compression ({a} : Finset α) ∅ 𝒜) := by
-- proof
  apply StatMech.fmarg_le_upCompression hw0 a hdom 𝒜

/--
[fmarg_le_doubleCompress](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressionClose.lean)
-/
@[path]
private lemma fmarg_le_doubleCompress_eq
  [Fintype α]
  [DecidableEq α]
  [Fintype β]
  [DecidableEq β]
  {w : (β ⊕ β) → Bool → ℝ}
  {i : β}
  {𝒰 : Finset (Finset (β ⊕ β))}
-- given
  (hw0 : ∀ x b, 0 ≤ w x b)
  (hL : w (Sum.inl i) true ≤ w (Sum.inl i) false)
  (hR : w (Sum.inr i) false ≤ w (Sum.inr i) true) :
-- imply
  fmarg w 𝒰 ≤ fmarg w (doubleCompress i 𝒰) := by
-- proof
  apply StatMech.fmarg_le_doubleCompress hw0 i hL hR 𝒰

/--
[iterDoubleCompress_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressionClose.lean)
-/
@[path]
private lemma iterDoubleCompress_nil_eq
  [Fintype α]
  [DecidableEq α]
  [Fintype β]
  [DecidableEq β]
  {𝒰 : Finset (Finset (β ⊕ β))} :
-- imply
  iterDoubleCompress [] 𝒰 = 𝒰 := by
-- proof
  apply StatMech.iterDoubleCompress_nil 𝒰

/--
[iterDoubleCompress_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressionClose.lean)
-/
@[path]
private lemma iterDoubleCompress_cons_eq
  [Fintype α]
  [DecidableEq α]
  [Fintype β]
  [DecidableEq β]
  {i : β}
  {is : List β}
  {𝒰 : Finset (Finset (β ⊕ β))} :
-- imply
  iterDoubleCompress (i :: is) 𝒰 = doubleCompress i (iterDoubleCompress is 𝒰) := by
-- proof
  apply StatMech.iterDoubleCompress_cons i is 𝒰

/--
[iterDoubleCompress_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressionClose.lean)
-/
@[path]
private lemma iterDoubleCompress_card_eq
  [Fintype α]
  [DecidableEq α]
  [Fintype β]
  [DecidableEq β]
  {is : List β}
  {𝒰 : Finset (Finset (β ⊕ β))} :
-- imply
  (iterDoubleCompress is 𝒰).card = 𝒰.card := by
-- proof
  apply StatMech.iterDoubleCompress_card is 𝒰

/--
[fmarg_le_iterDoubleCompress](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressionClose.lean)
-/
@[path]
private lemma fmarg_le_iterDoubleCompress_eq
  [Fintype α]
  [DecidableEq α]
  [Fintype β]
  [DecidableEq β]
  {w : (β ⊕ β) → Bool → ℝ}
  {is : List β}
  {𝒰 : Finset (Finset (β ⊕ β))}
-- given
  (hw0 : ∀ x b, 0 ≤ w x b)
  (hL : ∀ i, w (Sum.inl i) true ≤ w (Sum.inl i) false)
  (hR : ∀ i, w (Sum.inr i) false ≤ w (Sum.inr i) true) :
-- imply
  fmarg w 𝒰 ≤ fmarg w (iterDoubleCompress is 𝒰) := by
-- proof
  apply StatMech.fmarg_le_iterDoubleCompress hw0 hL hR is 𝒰

/--
[fmarg_le_downCompression_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressionClose.lean)
-/
@[path]
private lemma fmarg_le_downCompression_satisfiable_eq
  [Fintype α]
  [DecidableEq α]
  [Fintype β]
  [DecidableEq β]
  {a : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  fmarg (fun _ _ => (1 : ℝ)) 𝒜 ≤ fmarg (fun _ _ => (1 : ℝ)) (Down.compression a 𝒜) := by
-- proof
  apply StatMech.fmarg_le_downCompression_satisfiable a 𝒜

/--
[fmarg_le_doubleCompress_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressionClose.lean)
-/
@[path]
private lemma fmarg_le_doubleCompress_symm_eq
  [Fintype α]
  [DecidableEq α]
  [Fintype β]
  [DecidableEq β]
  {w : (β ⊕ β) → Bool → ℝ}
  {i : β}
  {𝒰 : Finset (Finset (β ⊕ β))}
-- given
  (hw0 : ∀ x b, 0 ≤ w x b)
  (hsym : ∀ x, w x false = w x true) :
-- imply
  fmarg w 𝒰 ≤ fmarg w (doubleCompress i 𝒰) := by
-- proof
  apply StatMech.fmarg_le_doubleCompress_symm hw0 hsym i 𝒰

/--
[fmarg_doubleCompress_symm_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressionClose.lean)
-/
@[path]
private lemma fmarg_doubleCompress_symm_eq_eq
  [Fintype α]
  [DecidableEq α]
  [Fintype β]
  [DecidableEq β]
  {w : (β ⊕ β) → Bool → ℝ}
  {i : β}
  {𝒰 : Finset (Finset (β ⊕ β))}
-- given
  (hsym : ∀ x, w x false = w x true) :
-- imply
  fmarg w (doubleCompress i 𝒰) = fmarg w 𝒰 := by
-- proof
  apply StatMech.fmarg_doubleCompress_symm_eq hsym i 𝒰

/--
[fmarg_boxDoubled_doubleWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressionClose.lean)
-/
@[path]
private lemma fmarg_boxDoubled_doubleWeight_eq
  [Fintype α]
  [DecidableEq α]
  [Fintype β]
  [DecidableEq β]
  {w : β → Bool → ℝ}
  {𝒜 ℬ : Finset (Finset β)} :
-- imply
  fmarg (doubleWeight w) (boxDoubled 𝒜 ℬ) = wdpairs w 𝒜 ℬ := by
-- proof
  apply StatMech.fmarg_boxDoubled_doubleWeight w 𝒜 ℬ

/--
[wdpairs_le_iterDoubleCompress_of_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressionClose.lean)
-/
@[path]
private lemma wdpairs_le_iterDoubleCompress_of_symm_eq
  [Fintype α]
  [DecidableEq α]
  [Fintype β]
  [DecidableEq β]
  {w : β → Bool → ℝ}
  {is : List β}
  {𝒜 ℬ : Finset (Finset β)}
-- given
  (hw0 : ∀ x b, 0 ≤ w x b)
  (hsym : ∀ x, w x false = w x true) :
-- imply
  wdpairs w 𝒜 ℬ ≤ fmarg (doubleWeight w) (iterDoubleCompress is (boxDoubled 𝒜 ℬ)) := by
-- proof
  apply StatMech.wdpairs_le_iterDoubleCompress_of_symm hw0 hsym is 𝒜 ℬ

/--
[wdpairs_le_mul_of_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressionClose.lean)
-/
@[path]
private lemma wdpairs_le_mul_of_symm_eq
  [Fintype α]
  [DecidableEq α]
  [Fintype β]
  [DecidableEq β]
  {w : β → Bool → ℝ}
  {𝒜 ℬ : Finset (Finset β)}
-- given
  (hw0 : ∀ x b, 0 ≤ w x b)
  (hw1 : ∀ x, w x false + w x true = 1) :
-- imply
  wdpairs w 𝒜 ℬ ≤ fmarg w 𝒜 * fmarg w ℬ := by
-- proof
  apply StatMech.wdpairs_le_mul_of_symm hw0 hw1 𝒜 ℬ


-- created on 2026-10-23
