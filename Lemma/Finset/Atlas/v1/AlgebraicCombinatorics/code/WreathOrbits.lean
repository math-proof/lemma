import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.WreathOrbits.Part5
open WreathOrbits


namespace WreathOrbits

/--
[WreathElem.actOn_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
lemma WreathElem.actOn_injective
  {m n : ℕ}
  {g : WreathElem m n} :
-- imply
  Function.Injective g.actOn := by
-- proof
  intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
  simp only [WreathElem.actOn, Prod.mk.injEq] at h
  have hi : i₁ = i₂ := g.σ.injective h.1
  subst hi; exact Prod.ext rfl (by exact (g.τ i₁).injective h.2)

end WreathOrbits

namespace WreathOrbits

/--
[exists_gridYoung_of_rowSizeMultiset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
lemma exists_gridYoung_of_rowSizeMultiset
  {m n : ℕ}
  {S : Finset (Fin m × Fin n)} :
-- imply
  ∃ T : Finset (Fin m × Fin n), IsGridYoung T ∧ rowSizeMultiset T = rowSizeMultiset S :=
-- proof
  ⟨canonicalYoung S, canonicalYoung_isGridYoung S, rowSizeMultiset_canonicalYoung S⟩

end WreathOrbits

namespace WreathOrbits

/--
[existsUnique_gridYoung_sameOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
lemma existsUnique_gridYoung_sameOrbit
  {m n : ℕ}
  {S : Finset (Fin m × Fin n)} :
-- imply
  ∃! T : Finset (Fin m × Fin n), IsGridYoung T ∧ SameOrbit S T := by
-- proof
  obtain ⟨T, hTy, hTm⟩ := exists_gridYoung_of_rowSizeMultiset S
  refine ⟨T, ⟨hTy, (sameOrbit_iff_rowSizeMultiset_eq S T).mpr hTm.symm⟩, ?_⟩
  intro T' ⟨hT'y, hT'o⟩
  have hT'o' := (sameOrbit_iff_rowSizeMultiset_eq S T').mp hT'o
  exact gridYoung_unique hT'y hTy (hT'o'.symm.trans hTm.symm)

end WreathOrbits

/--
[rowSize_actOnSet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
private lemma rowSize_actOnSet_eq
  {m n : ℕ}
  {g : WreathElem m n}
  {S : Finset (Fin m × Fin n)}
  {i : Fin m} :
-- imply
  rowSize (g.actOnSet S) (g.σ i) = rowSize S i := by
-- proof
  apply WreathOrbits.rowSize_actOnSet g S i

/--
[mem_rowCols_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
private lemma mem_rowCols_iff_eq
  {m n : ℕ}
  {S : Finset (Fin m × Fin n)}
  {i : Fin m}
  {j : Fin n} :
-- imply
  j ∈ rowCols S i ↔ (i, j) ∈ S := by
-- proof
  apply WreathOrbits.mem_rowCols_iff S i j

/--
[rowCols_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
private lemma rowCols_card_eq
  {m n : ℕ}
  {S : Finset (Fin m × Fin n)}
  {i : Fin m} :
-- imply
  (rowCols S i).card = rowSize S i := by
-- proof
  apply WreathOrbits.rowCols_card S i

/--
[exists_perm_image_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
private lemma exists_perm_image_eq_eq
  {m n : ℕ}
  {A B : Finset (Fin n)}
-- given
  (h : A.card = B.card) :
-- imply
  ∃ σ : Equiv.Perm (Fin n), A.image σ = B := by
-- proof
  apply WreathOrbits.exists_perm_image_eq A B h

/--
[fiber_card_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
private lemma fiber_card_eq_eq
  {m n : ℕ}
  {S T : Finset (Fin m × Fin n)}
  {v : ℕ}
-- given
  (h : rowSizeMultiset S = rowSizeMultiset T) :
-- imply
  Fintype.card {i : Fin m // rowSize S i = v} = Fintype.card {i : Fin m // rowSize T i = v} := by
-- proof
  apply WreathOrbits.fiber_card_eq S T h v

/--
[rowSizeMultiset_eq_of_sameOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
private lemma rowSizeMultiset_eq_of_sameOrbit_eq
  {m n : ℕ}
  {S T : Finset (Fin m × Fin n)}
-- given
  (h : SameOrbit S T) :
-- imply
  rowSizeMultiset S = rowSizeMultiset T := by
-- proof
  apply WreathOrbits.rowSizeMultiset_eq_of_sameOrbit S T h

/--
[sameOrbit_of_rowSizeMultiset_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
private lemma sameOrbit_of_rowSizeMultiset_eq_eq
  {m n : ℕ}
  {S T : Finset (Fin m × Fin n)}
-- given
  (h : rowSizeMultiset S = rowSizeMultiset T) :
-- imply
  SameOrbit S T := by
-- proof
  apply WreathOrbits.sameOrbit_of_rowSizeMultiset_eq S T h

/--
[sameOrbit_iff_rowSizeMultiset_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
private lemma sameOrbit_iff_rowSizeMultiset_eq_eq
  {m n : ℕ}
  {S T : Finset (Fin m × Fin n)} :
-- imply
  SameOrbit S T ↔ rowSizeMultiset S = rowSizeMultiset T := by
-- proof
  apply WreathOrbits.sameOrbit_iff_rowSizeMultiset_eq S T

/--
[rowSize_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
private lemma rowSize_le_eq
  {m n : ℕ}
  {S : Finset (Fin m × Fin n)}
  {i : Fin m} :
-- imply
  rowSize S i ≤ n := by
-- proof
  apply WreathOrbits.rowSize_le S i

/--
[mem_iff_lt_rowSize](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
private lemma mem_iff_lt_rowSize_eq
  {m n : ℕ}
  {S : Finset (Fin m × Fin n)}
  {i : Fin m}
  {j : Fin n}
-- given
  (hS : IsLeftJustified S) :
-- imply
  (i, j) ∈ S ↔ j.val < rowSize S i := by
-- proof
  apply WreathOrbits.mem_iff_lt_rowSize hS i j

/--
[leftJustified_eq_of_rowSize_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
private lemma leftJustified_eq_of_rowSize_eq_eq
  {m n : ℕ}
  {S T : Finset (Fin m × Fin n)}
-- given
  (hS : IsLeftJustified S)
  (hT : IsLeftJustified T)
  (h : ∀ i, rowSize S i = rowSize T i) :
-- imply
  S = T := by
-- proof
  apply WreathOrbits.leftJustified_eq_of_rowSize_eq hS hT h

/--
[map_finRange_pairwise_ge](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
private lemma map_finRange_pairwise_ge_eq
  {m n : ℕ}
  {f : Fin m → ℕ}
-- given
  (hf : Antitone f) :
-- imply
  ((List.finRange m).map f).Pairwise (· ≥ ·) := by
-- proof
  apply WreathOrbits.map_finRange_pairwise_ge hf

/--
[univ_val_eq_coe_finRange](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
private lemma univ_val_eq_coe_finRange_eq
  {m n : ℕ} :
-- imply
  (Finset.univ : Finset (Fin m)).val = ↑(List.finRange m) := by
-- proof
  apply WreathOrbits.univ_val_eq_coe_finRange

/--
[antitone_eq_of_multiset_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
private lemma antitone_eq_of_multiset_eq_eq
  {m n : ℕ}
  {f g : Fin m → ℕ}
-- given
  (hf : Antitone f)
  (hg : Antitone g)
  (h : Finset.univ.val.map f = Finset.univ.val.map g) :
-- imply
  f = g := by
-- proof
  apply WreathOrbits.antitone_eq_of_multiset_eq hf hg h

/--
[gridYoung_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
private lemma gridYoung_unique_eq
  {m n : ℕ}
  {S T : Finset (Fin m × Fin n)}
-- given
  (hS : IsGridYoung S)
  (hT : IsGridYoung T)
  (h : rowSizeMultiset S = rowSizeMultiset T) :
-- imply
  S = T := by
-- proof
  apply WreathOrbits.gridYoung_unique hS hT h

/--
[sortedRowSizes_length](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
private lemma sortedRowSizes_length_eq
  {m n : ℕ}
  {S : Finset (Fin m × Fin n)} :
-- imply
  (sortedRowSizes S).length = m := by
-- proof
  apply WreathOrbits.sortedRowSizes_length S

/--
[sortedRowSizes_pairwise](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
private lemma sortedRowSizes_pairwise_eq
  {m n : ℕ}
  {S : Finset (Fin m × Fin n)} :
-- imply
  (sortedRowSizes S).Pairwise (· ≥ ·) := by
-- proof
  apply WreathOrbits.sortedRowSizes_pairwise S

/--
[sortedRowSizes_multiset_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
private lemma sortedRowSizes_multiset_eq_eq
  {m n : ℕ}
  {S : Finset (Fin m × Fin n)} :
-- imply
  ↑(sortedRowSizes S) = Finset.univ.val.map (rowSize S) := by
-- proof
  apply WreathOrbits.sortedRowSizes_multiset_eq S

/--
[sortedRowSizes_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
private lemma sortedRowSizes_le_eq
  {m n : ℕ}
  {S : Finset (Fin m × Fin n)}
  {k : ℕ}
-- given
  (hk : k < (sortedRowSizes S).length) :
-- imply
  (sortedRowSizes S)[k] ≤ n := by
-- proof
  apply WreathOrbits.sortedRowSizes_le S k hk

/--
[getD_le_n](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
private lemma getD_le_n_eq
  {m n : ℕ}
  {S : Finset (Fin m × Fin n)}
  {i : Fin m} :
-- imply
  (sortedRowSizes S).getD i.val 0 ≤ n := by
-- proof
  apply WreathOrbits.getD_le_n S i

/--
[mem_canonicalYoung](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
private lemma mem_canonicalYoung_eq
  {m n : ℕ}
  {S : Finset (Fin m × Fin n)}
  {i : Fin m}
  {j : Fin n} :
-- imply
  (i, j) ∈ canonicalYoung S ↔ j.val < (sortedRowSizes S).getD i.val 0 := by
-- proof
  apply WreathOrbits.mem_canonicalYoung S i j

/--
[canonicalYoung_isLeftJustified](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
private lemma canonicalYoung_isLeftJustified_eq
  {m n : ℕ}
  {S : Finset (Fin m × Fin n)} :
-- imply
  IsLeftJustified (canonicalYoung S) := by
-- proof
  apply WreathOrbits.canonicalYoung_isLeftJustified S

/--
[filter_lt_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
private lemma filter_lt_card_eq
  {m n : ℕ}
  {k : Fin (n + 1)} :
-- imply
  ((Finset.univ : Finset (Fin n)).filter (fun x : Fin n => (x : ℕ) < (k : ℕ))).card = k.val := by
-- proof
  apply WreathOrbits.filter_lt_card k

/--
[rowSize_canonicalYoung](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
private lemma rowSize_canonicalYoung_eq
  {m n : ℕ}
  {S : Finset (Fin m × Fin n)}
  {i : Fin m} :
-- imply
  rowSize (canonicalYoung S) i = (sortedRowSizes S).getD i.val 0 := by
-- proof
  apply WreathOrbits.rowSize_canonicalYoung S i

/--
[canonicalYoung_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
private lemma canonicalYoung_antitone_eq
  {m n : ℕ}
  {S : Finset (Fin m × Fin n)} :
-- imply
  Antitone (rowSize (canonicalYoung S)) := by
-- proof
  apply WreathOrbits.canonicalYoung_antitone S

/--
[canonicalYoung_isGridYoung](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
private lemma canonicalYoung_isGridYoung_eq
  {m n : ℕ}
  {S : Finset (Fin m × Fin n)} :
-- imply
  IsGridYoung (canonicalYoung S) := by
-- proof
  apply WreathOrbits.canonicalYoung_isGridYoung S

/--
[finRange_map_getD](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
private lemma finRange_map_getD_eq
  {m n : ℕ}
  {l : List ℕ}
-- given
  (hl : l.length = m) :
-- imply
  (List.finRange m).map (fun i : Fin m => l.getD i.val 0) = l := by
-- proof
  apply WreathOrbits.finRange_map_getD l hl

/--
[map_getD_eq_coe](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
private lemma map_getD_eq_coe_eq
  {m n : ℕ}
  {l : List ℕ}
-- given
  (hl : l.length = m) :
-- imply
  Finset.univ.val.map (fun i : Fin m => l.getD i.val 0) = ↑l := by
-- proof
  apply WreathOrbits.map_getD_eq_coe l hl

/--
[rowSizeMultiset_canonicalYoung](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean)
-/
@[path]
private lemma rowSizeMultiset_canonicalYoung_eq
  {m n : ℕ}
  {S : Finset (Fin m × Fin n)} :
-- imply
  rowSizeMultiset (canonicalYoung S) = rowSizeMultiset S := by
-- proof
  apply WreathOrbits.rowSizeMultiset_canonicalYoung S


-- created on 2026-10-23
