import sympy.Basic


@[path]
private lemma nonoverlapping.condlimit.utility
  [DecidableEq α]
  {n : ℕ}
  {x : ℕ → Finset α}
-- given
  (h : ∀ i j, j ≠ i → x i ∩ x j = ∅) :
-- imply
  ((Finset.range n).biUnion x).card = ∑ i ∈ Finset.range n, (x i).card := by
-- proof
  apply Finset.card_biUnion
  intro i _ j _ hij
  exact Finset.disjoint_iff_inter_eq_empty.mpr (h i j (Ne.symm hij))


@[path]
private lemma nonoverlapping.intlimit.utility
  [DecidableEq α]
  {n : ℕ}
  {x : ℕ → Finset α}
-- given
  (h : ∀ i, ∀ j < i, x i ∩ x j = ∅) :
-- imply
  ((Finset.range n).biUnion x).card = ∑ i ∈ Finset.range n, (x i).card := by
-- proof
  apply Finset.card_biUnion
  intro i _ j _ hij
  apply Finset.disjoint_iff_inter_eq_empty.mpr
  rcases lt_or_gt_of_ne hij with hlt | hlt
  ·
    rw [Finset.inter_comm]
    exact h j i hlt
  ·
    exact h i j hlt


@[path]
private lemma nonoverlapping.setlimit
  [DecidableEq α]
  {n : ℕ}
  {x : ℕ → Finset α}
-- given
  (h : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n \ {i}, x i ∩ x j = ∅) :
-- imply
  ((Finset.range n).biUnion x).card = ∑ i ∈ Finset.range n, (x i).card := by
-- proof
  apply Finset.card_biUnion
  intro i hi j hj hij
  apply Finset.disjoint_iff_inter_eq_empty.mpr
  apply h i (by simpa using hi) j
  simp only [Finset.mem_sdiff, Finset.mem_singleton]
  exact ⟨by simpa using hj, fun h' => hij h'.symm⟩


@[path]
private lemma nonoverlapping.intlimit
  [DecidableEq α]
  {n : ℕ}
  {x : ℕ → Finset α}
-- given
  (h : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n \ {i}, x i ∩ x j = ∅) :
-- imply
  ((Finset.range n).biUnion x).card = ∑ i ∈ Finset.range n, (x i).card := by
-- proof
  apply Finset.card_biUnion
  intro i hi j hj hij
  apply Finset.disjoint_iff_inter_eq_empty.mpr
  apply h i (by simpa using hi) j
  simp only [Finset.mem_sdiff, Finset.mem_singleton]
  exact ⟨by simpa using hj, fun h' => hij h'.symm⟩


@[path]
private lemma nonoverlapping.setlimit.utility
  [DecidableEq α]
  {n : ℕ}
  {x : ℕ → Finset α}
-- given
  (h : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n \ {i}, x i ∩ x j = ∅) :
-- imply
  ((Finset.range n).biUnion x).card = ∑ i ∈ Finset.range n, (x i).card := by
-- proof
  apply Finset.card_biUnion
  intro i hi j hj hij
  apply Finset.disjoint_iff_inter_eq_empty.mpr
  apply h i (by simpa using hi) j
  simp only [Finset.mem_sdiff, Finset.mem_singleton]
  exact ⟨by simpa using hj, fun h' => hij h'.symm⟩


-- created on 2026-09-27
