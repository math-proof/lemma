import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc90boxopenforest
open Set SimpleGraph Finset MeasureTheory StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc90_genuineTrif_iff_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc90boxopenforest.lean)
-/
@[path]
private lemma bc90_genuineTrif_iff_canonical_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d} :
-- imply
  bc89_GenuineTrif d ω x ↔ IsCanonicalTrifurcation d ω x := by
-- proof
  apply StatMech.Walls.bc90_genuineTrif_iff_canonical ω x

/--
[bc90_canonical_of_genuineTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc90boxopenforest.lean)
-/
@[path]
private lemma bc90_canonical_of_genuineTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (h : bc89_GenuineTrif d ω x) :
-- imply
  IsCanonicalTrifurcation d ω x := by
-- proof
  apply StatMech.Walls.bc90_canonical_of_genuineTrif ω x h

/--
[bc90_spanForest_preserves_genuineTrif_deg3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc90boxopenforest.lean)
-/
@[path]
private lemma bc90_spanForest_preserves_genuineTrif_deg3_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d}
-- given
  (hn : 1 ≤ n)
  (hxbox : x ∈ box d n)
  (hgen : bc89_GenuineTrif d ω x)
  (harmbox_x : ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n) :
-- imply
  ∃ c : Fin 3 → Site d, (c 0 ≠ c 1 ∧ c 0 ≠ c 2 ∧ c 1 ≠ c 2) ∧ (∀ i, (cfc_T ω n).Adj x (c i)) ∧ (¬ Connected d (removeSite x ω) (c 0) (c 1) ∧ ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧ ¬ Connected d (removeSite x ω) (c 1) (c 2)) := by
-- proof
  apply StatMech.Walls.bc90_spanForest_preserves_genuineTrif_deg3 ω n hn hxbox hgen harmbox_x

/--
[bc90_spanForest_subtype_deg3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc90boxopenforest.lean)
-/
@[path]
private lemma bc90_spanForest_subtype_deg3_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d}
  [DecidableRel (cfc_F ω n).Adj]
-- given
  (hn : 1 ≤ n)
  (hxbox : x ∈ box d n)
  (hgen : bc89_GenuineTrif d ω x)
  (harmbox_x : ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n) :
-- imply
  3 ≤ (cfc_F ω n).degree ⟨x, box_subset_succ d n hxbox⟩ := by
-- proof
  apply StatMech.Walls.bc90_spanForest_subtype_deg3 ω n hn hxbox hgen harmbox_x

/--
[bc90_boxOpenForest_of_genuine_armsInBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc90boxopenforest.lean)
-/
@[path]
private lemma bc90_boxOpenForest_of_genuine_armsInBox_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → bc89_GenuineTrif d ω x)
  (harmbox : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n)
  (hexists : ∃ x, x ∈ box d n ∧ IsTrifurcation d ω x) :
-- imply
  bst_BoxOpenForest ω n := by
-- proof
  apply StatMech.Walls.bc90_boxOpenForest_of_genuine_armsInBox ω n hn hcanon harmbox hexists

/--
[bc90_Tcount_le_boundary_of_genuine_armsInBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc90boxopenforest.lean)
-/
@[path]
private lemma bc90_Tcount_le_boundary_of_genuine_armsInBox_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → bc89_GenuineTrif d ω x)
  (harmbox : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc90_Tcount_le_boundary_of_genuine_armsInBox ω n hn hcanon harmbox

/--
[bc90_genuineTcount_le_boundary_of_genuine_armsInBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc90boxopenforest.lean)
-/
@[path]
private lemma bc90_genuineTcount_le_boundary_of_genuine_armsInBox_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → bc89_GenuineTrif d ω x)
  (harmbox : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n) :
-- imply
  bc89_genuineTcount ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc90_genuineTcount_le_boundary_of_genuine_armsInBox ω n hn hcanon harmbox

/--
[bc90_harmbox_free_of_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc90boxopenforest.lean)
-/
@[path]
private lemma bc90_harmbox_free_of_interior_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d}
  {a : Site d}
-- given
  (hn : 1 ≤ n)
  (hxint : x ∈ box d (n - 1))
  (hadj : (openSubgraph d ω).Adj x a) :
-- imply
  a ∈ box d n := by
-- proof
  apply StatMech.Walls.bc90_harmbox_free_of_interior ω hn hxint hadj

/--
[bc90_upperLines_boxOpenForest_count_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc90boxopenforest.lean)
-/
@[path]
private lemma bc90_upperLines_boxOpenForest_count_free_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  bc89_genuineTcount bc60_upperLines n = 0 ∧ bc89_genuineTcount bc60_upperLines n ≤ boxSV_boundaryCard 2 n := by
-- proof
  apply StatMech.Walls.bc90_upperLines_boxOpenForest_count_free n

/--
[bc90_boxOpenForest_star](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc90boxopenforest.lean)
-/
@[path]
private lemma bc90_boxOpenForest_star_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d}
  {a : Fin 3 → Site d}
-- given
  (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x)
  (hadj : ∀ i, (openSubgraph d ω).Adj x (a i))
  (habdry : ∀ i, a i ∈ vertexBoundary d n)
  (hxne : ∀ i, a i ≠ x)
  (hainj : Function.Injective a)
  (hsep : ¬ Connected d (removeSite x ω) (a 0) (a 1) ∧ ¬ Connected d (removeSite x ω) (a 0) (a 2) ∧ ¬ Connected d (removeSite x ω) (a 1) (a 2)) :
-- imply
  bst_BoxOpenForest ω n := by
-- proof
  apply StatMech.Walls.bc90_boxOpenForest_star ω n a hsingle hadj habdry hxne hainj hsep

/--
[bc90_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc90boxopenforest.lean)
-/
@[path]
private lemma bc90_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), 1 ≤ n → ∀ {x : Site 2}, x ∈ box 2 n → bc89_GenuineTrif 2 ω x → (∀ a, (openSubgraph 2 ω).Adj x a → (cluster 2 (removeSite x ω) a).Infinite → a ∈ box 2 n) → ∃ c : Fin 3 → Site 2, (c 0 ≠ c 1 ∧ c 0 ≠ c 2 ∧ c 1 ≠ c 2) ∧ (∀ i, (cfc_T ω n).Adj x (c i)) ∧ (¬ Connected 2 (removeSite x ω) (c 0) (c 1) ∧ ¬ Connected 2 (removeSite x ω) (c 0) (c 2) ∧ ¬ Connected 2 (removeSite x ω) (c 1) (c 2))) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), 1 ≤ n → ∀ {x : Site 2} (hxbox : x ∈ box 2 n), bc89_GenuineTrif 2 ω x → (∀ a, (openSubgraph 2 ω).Adj x a → (cluster 2 (removeSite x ω) a).Infinite → a ∈ box 2 n) → ∀ [DecidableRel (cfc_F ω n).Adj], 3 ≤ (cfc_F ω n).degree ⟨x, box_subset_succ 2 n hxbox⟩) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), 1 ≤ n → (∀ x, x ∈ box 2 n → IsTrifurcation 2 ω x → bc89_GenuineTrif 2 ω x) → (∀ x, x ∈ box 2 n → IsTrifurcation 2 ω x → ∀ a, (openSubgraph 2 ω).Adj x a → (cluster 2 (removeSite x ω) a).Infinite → a ∈ box 2 n) → (∃ x, x ∈ box 2 n ∧ IsTrifurcation 2 ω x) → bst_BoxOpenForest ω n) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), 1 ≤ n → (∀ x, x ∈ box 2 n → IsTrifurcation 2 ω x → bc89_GenuineTrif 2 ω x) → (∀ x, x ∈ box 2 n → IsTrifurcation 2 ω x → ∀ a, (openSubgraph 2 ω).Adj x a → (cluster 2 (removeSite x ω) a).Infinite → a ∈ box 2 n) → Tcount 2 ω n ≤ boxSV_boundaryCard 2 n) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), 1 ≤ n → ∀ {x : Site 2}, x ∈ box 2 (n - 1) → ∀ {a : Site 2}, (openSubgraph 2 ω).Adj x a → a ∈ box 2 n) ∧ (∀ n : ℕ, bc89_genuineTcount bc60_upperLines n = 0 ∧ bc89_genuineTcount bc60_upperLines n ≤ boxSV_boundaryCard 2 n) := by
-- proof
  apply StatMech.Walls.bc90_status


-- created on 2026-10-23
