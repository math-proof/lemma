import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicCombinatorics.code.QuotientIsoLmn.Part7
open WreathOrbits YoungLattice YoungLattice.Lmn QuotientIsoLmn


/--
[mem_lmnToFinset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientIsoLmn.lean)
-/
@[path]
private lemma mem_lmnToFinset_eq
  {m n : ℕ}
  {p : Lmn m n}
  {i : Fin m}
  {j : Fin n} :
-- imply
  (i, j) ∈ lmnToFinset p ↔ j.val < (p.val i).val := by
-- proof
  apply QuotientIsoLmn.mem_lmnToFinset p i j

/--
[lmnToFinset_isLeftJustified](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientIsoLmn.lean)
-/
@[path]
private lemma lmnToFinset_isLeftJustified_eq
  {m n : ℕ}
  {p : Lmn m n} :
-- imply
  WreathOrbits.IsLeftJustified (lmnToFinset p) := by
-- proof
  apply QuotientIsoLmn.lmnToFinset_isLeftJustified p

/--
[lmnToFinset_rowSize](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientIsoLmn.lean)
-/
@[path]
private lemma lmnToFinset_rowSize_eq
  {m n : ℕ}
  {p : Lmn m n}
  {i : Fin m} :
-- imply
  WreathOrbits.rowSize (lmnToFinset p) i = (p.val i).val := by
-- proof
  apply QuotientIsoLmn.lmnToFinset_rowSize p i

/--
[lmnToFinset_isGridYoung](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientIsoLmn.lean)
-/
@[path]
private lemma lmnToFinset_isGridYoung_eq
  {m n : ℕ}
  {p : Lmn m n} :
-- imply
  WreathOrbits.IsGridYoung (lmnToFinset p) := by
-- proof
  apply QuotientIsoLmn.lmnToFinset_isGridYoung p

/--
[gridYoungToLmn_lmnToGridYoung](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientIsoLmn.lean)
-/
@[path]
private lemma gridYoungToLmn_lmnToGridYoung_eq
  {m n : ℕ}
  {p : Lmn m n} :
-- imply
  gridYoungToLmn (lmnToGridYoung p) = p := by
-- proof
  apply QuotientIsoLmn.gridYoungToLmn_lmnToGridYoung p

/--
[lmnToGridYoung_gridYoungToLmn](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientIsoLmn.lean)
-/
@[path]
private lemma lmnToGridYoung_gridYoungToLmn_eq
  {m n : ℕ}
  {S : GridYoungDiagram m n} :
-- imply
  lmnToGridYoung (gridYoungToLmn S) = S := by
-- proof
  apply QuotientIsoLmn.lmnToGridYoung_gridYoungToLmn S

/--
[rowSize_le_of_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientIsoLmn.lean)
-/
@[path]
private lemma rowSize_le_of_subset_eq
  {m n : ℕ}
  {S T : Finset (Fin m × Fin n)}
  {i : Fin m}
-- given
  (hST : S ⊆ T) :
-- imply
  WreathOrbits.rowSize S i ≤ WreathOrbits.rowSize T i := by
-- proof
  apply QuotientIsoLmn.rowSize_le_of_subset hST i

/--
[gridYoungToLmn_le_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientIsoLmn.lean)
-/
@[path]
private lemma gridYoungToLmn_le_iff_eq
  {m n : ℕ}
  {S T : GridYoungDiagram m n} :
-- imply
  gridYoungToLmn S ≤ gridYoungToLmn T ↔ S ≤ T := by
-- proof
  apply QuotientIsoLmn.gridYoungToLmn_le_iff S T

/--
[card_eq_of_sameOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientIsoLmn.lean)
-/
@[path]
private lemma card_eq_of_sameOrbit_eq
  {m n : ℕ}
  {S T : Finset (Fin m × Fin n)}
-- given
  (h : WreathOrbits.SameOrbit S T) :
-- imply
  S.card = T.card := by
-- proof
  apply QuotientIsoLmn.card_eq_of_sameOrbit h

/--
[wreathQuotientMk_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientIsoLmn.lean)
-/
@[path]
private lemma wreathQuotientMk_eq_iff_eq
  {m n : ℕ}
  {S T : Finset (Fin m × Fin n)} :
-- imply
  wreathQuotientMk S = wreathQuotientMk T ↔ WreathOrbits.SameOrbit S T := by
-- proof
  apply QuotientIsoLmn.wreathQuotientMk_eq_iff S T

/--
[actOnSet_subset_of_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientIsoLmn.lean)
-/
@[path]
private lemma actOnSet_subset_of_subset_eq
  {m n : ℕ}
  {g : WreathElem m n}
  {S T : Finset (Fin m × Fin n)}
-- given
  (h : S ⊆ T) :
-- imply
  g.actOnSet S ⊆ g.actOnSet T := by
-- proof
  apply QuotientIsoLmn.actOnSet_subset_of_subset g h

/--
[wreathQuotientMk_actOnSet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientIsoLmn.lean)
-/
@[path]
private lemma wreathQuotientMk_actOnSet_eq
  {m n : ℕ}
  {g : WreathElem m n}
  {S : Finset (Fin m × Fin n)} :
-- imply
  wreathQuotientMk (g.actOnSet S) = wreathQuotientMk S := by
-- proof
  apply QuotientIsoLmn.wreathQuotientMk_actOnSet g S

/--
[finset_filter_card_eq_sorted_filter_length](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientIsoLmn.lean)
-/
@[path]
private lemma finset_filter_card_eq_sorted_filter_length_eq
  {m n : ℕ}
  {S : Finset (Fin m × Fin n)}
  [DecidablePred p]
-- given
  (p : ℕ → Prop) :
-- imply
  (Finset.univ.filter (fun i : Fin m => p (WreathOrbits.rowSize S i))).card = ((WreathOrbits.sortedRowSizes S).filter (fun x => decide (p x))).length := by
-- proof
  apply QuotientIsoLmn.finset_filter_card_eq_sorted_filter_length S p

/--
[card_filter_ge_of_sorted](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientIsoLmn.lean)
-/
@[path]
private lemma card_filter_ge_of_sorted_eq
  {m n : ℕ}
  {S : Finset (Fin m × Fin n)}
  {k : Fin m}
  {v : ℕ}
-- given
  (hv : v ≤ (WreathOrbits.sortedRowSizes S).getD k.val 0) :
-- imply
  k.val + 1 ≤ (Finset.univ.filter (fun i : Fin m => v ≤ WreathOrbits.rowSize S i)).card := by
-- proof
  apply QuotientIsoLmn.card_filter_ge_of_sorted k v hv

/--
[card_filter_ge_le_of_sorted](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientIsoLmn.lean)
-/
@[path]
private lemma card_filter_ge_le_of_sorted_eq
  {m n : ℕ}
  {T : Finset (Fin m × Fin n)}
  {k : Fin m}
  {v : ℕ}
-- given
  (hv : (WreathOrbits.sortedRowSizes T).getD k.val 0 < v) :
-- imply
  (Finset.univ.filter (fun i : Fin m => v ≤ WreathOrbits.rowSize T i)).card ≤ k.val := by
-- proof
  apply QuotientIsoLmn.card_filter_ge_le_of_sorted k v hv

/--
[sortedRowSizes_le_of_rowSize_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientIsoLmn.lean)
-/
@[path]
private lemma sortedRowSizes_le_of_rowSize_le_eq
  {m n : ℕ}
  {S T : Finset (Fin m × Fin n)}
  {k : Fin m}
-- given
  (h : ∀ i, WreathOrbits.rowSize S i ≤ WreathOrbits.rowSize T i) :
-- imply
  (WreathOrbits.sortedRowSizes S).getD k.val 0 ≤ (WreathOrbits.sortedRowSizes T).getD k.val 0 := by
-- proof
  apply QuotientIsoLmn.sortedRowSizes_le_of_rowSize_le S T h k

/--
[canonicalYoung_subset_of_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientIsoLmn.lean)
-/
@[path]
private lemma canonicalYoung_subset_of_subset_eq
  {m n : ℕ}
  {S T : Finset (Fin m × Fin n)}
-- given
  (h : S ⊆ T) :
-- imply
  WreathOrbits.canonicalYoung S ⊆ WreathOrbits.canonicalYoung T := by
-- proof
  apply QuotientIsoLmn.canonicalYoung_subset_of_subset h

/--
[canonicalYoung_eq_of_sameOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientIsoLmn.lean)
-/
@[path]
private lemma canonicalYoung_eq_of_sameOrbit_eq
  {m n : ℕ}
  {S T : Finset (Fin m × Fin n)}
-- given
  (h : WreathOrbits.SameOrbit S T) :
-- imply
  WreathOrbits.canonicalYoung S = WreathOrbits.canonicalYoung T := by
-- proof
  apply QuotientIsoLmn.canonicalYoung_eq_of_sameOrbit h

/--
[canonicalYoung_sameOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientIsoLmn.lean)
-/
@[path]
private lemma canonicalYoung_sameOrbit_eq
  {m n : ℕ}
  {S : Finset (Fin m × Fin n)} :
-- imply
  WreathOrbits.SameOrbit S (WreathOrbits.canonicalYoung S) := by
-- proof
  apply QuotientIsoLmn.canonicalYoung_sameOrbit S

/--
[gridYoungToWreathQuotient_wreathQuotientToGridYoung](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientIsoLmn.lean)
-/
@[path]
private lemma gridYoungToWreathQuotient_wreathQuotientToGridYoung_eq
  {m n : ℕ} :
-- imply
  ∀ q : WreathQuotient m n, gridYoungToWreathQuotient (wreathQuotientToGridYoung q) = q := by
-- proof
  apply QuotientIsoLmn.gridYoungToWreathQuotient_wreathQuotientToGridYoung

/--
[wreathQuotientToGridYoung_gridYoungToWreathQuotient](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientIsoLmn.lean)
-/
@[path]
private lemma wreathQuotientToGridYoung_gridYoungToWreathQuotient_eq
  {m n : ℕ} :
-- imply
  ∀ D : GridYoungDiagram m n, wreathQuotientToGridYoung (gridYoungToWreathQuotient D) = D := by
-- proof
  apply QuotientIsoLmn.wreathQuotientToGridYoung_gridYoungToWreathQuotient

/--
[wreathQuotientToGridYoung_le_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientIsoLmn.lean)
-/
@[path]
private lemma wreathQuotientToGridYoung_le_iff_eq
  {m n : ℕ}
  {a b : WreathQuotient m n} :
-- imply
  wreathQuotientToGridYoung a ≤ wreathQuotientToGridYoung b ↔ a ≤ b := by
-- proof
  apply QuotientIsoLmn.wreathQuotientToGridYoung_le_iff a b


-- created on 2026-10-23
