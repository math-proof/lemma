/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Reversal.lean -/

import sympy.atlas.NumberTheory.MultipleZeta.Series
/-!
# Reversing multiple-zeta summation conventions

Multiple-zeta values are commonly written using either strictly increasing
summation variables, with the final exponent at least two, or strictly
decreasing summation variables, with the first exponent at least two. This
module defines the increasing presentation and proves that reversing both the
exponent index and the summation tuple identifies it with `strictValue`.

## Main definitions

* `Index.reverse` reverses the exponent index.
* `Index.IsIncreasingAdmissible` expresses admissibility in the increasing convention.
* `StrictIncreasingTuple` is a strictly increasing tuple of positive naturals.
* `increasingSummand` and `increasingValue` give the increasing presentation.
* `increasingEquivDecreasing` reverses an increasing tuple.

## Main results

* `Index.isIncreasingAdmissible_iff_reverse_isAdmissible` transports admissibility.
* `increasingSummand_eq_strictSummand_reverse` identifies individual summands.
* `increasingValue_eq_strictValue_reverse` identifies the two series.

## References

* [K.-W. Chen et al., *Some Symmetry and Duality Theorems on Multiple
  Zeta(-star) Values*](https://arxiv.org/abs/2304.08722)
* [N. Tamang and P. Sarkar, *An algebraic proof of the duality of multiple
  zeta-star values of height one*](https://arxiv.org/abs/2307.09867)
* [Z. Li, Z. Wang, and L. Zhang, *A proof of a weighted sum conjecture for
  finite multiple zeta values of level two*](https://arxiv.org/abs/2608.10675)
* [H. Bachmann and Risan, *Formal finite multiple zeta
  values*](https://arxiv.org/abs/2608.15480)
-/

namespace MetaMathlibExt.MultipleZeta

/-- Reverse the exponent entries of a multiple-zeta index. -/
def Index.reverse (index : Index) : Index :=
  match index with
  | ⟨n, composition⟩ => ⟨n, composition.reverse⟩

@[simp]
theorem Index.reverse_entries (index : Index) :
    index.reverse.entries = index.entries.reverse := by
  rcases index with ⟨n, composition⟩
  simp [Index.entries, Index.reverse, Composition.reverse_blocks]

@[simp]
theorem Index.reverse_weight (index : Index) :
    index.reverse.weight = index.weight := by
  rcases index with ⟨n, composition⟩
  rfl

@[simp]
theorem Index.reverse_depth (index : Index) :
    index.reverse.depth = index.depth := by
  rcases index with ⟨n, composition⟩
  change composition.reverse.blocks.length = composition.blocks.length
  simp

@[simp]
theorem Index.reverse_reverse (index : Index) :
    index.reverse.reverse = index := by
  rcases index with ⟨n, composition⟩
  simp only [Index.reverse]
  rw [Composition.reverse_reverse]

/-- Strictly increasing tuples of positive naturals used in the increasing
multiple-zeta convention. -/
abbrev StrictIncreasingTuple (depth : ℕ) :=
  {m : Fin depth → PNat // StrictMono m}

/-- Admissibility in the increasing convention: the last exponent is at least two.
This is the convention in arXiv:2304.08722 and arXiv:2608.10675. -/
def Index.IsIncreasingAdmissible (index : Index) : Prop :=
  MetaMathlibExt.MultipleZeta.IsAdmissible index.entries.reverse

/-- Increasing admissibility is decreasing admissibility after reversing the index. -/
theorem Index.isIncreasingAdmissible_iff_reverse_isAdmissible (index : Index) :
    index.IsIncreasingAdmissible ↔ index.reverse.IsAdmissible := by
  rw [Index.isAdmissible_iff, Index.reverse_entries]
  rfl

private theorem composition_blocksFun_reverse {n : ℕ}
    (composition : Composition n)
    (i : Fin composition.reverse.blocks.length) :
    Composition.blocksFun composition.reverse i =
      Composition.blocksFun composition
        (Fin.rev (Fin.castOrderIso (by simp) i)) := by
  simp only [Composition.blocksFun, Composition.reverse_blocks,
    List.get_eq_getElem, List.getElem_reverse, Fin.val_rev, Nat.sub_sub]
  apply getElem_congr rfl
  change composition.blocks.length - (1 + i.val) =
    composition.blocks.length - (i.val + 1)
  omega

/-- An entry in the reversed index is the corresponding entry counted from
the other end. -/
theorem Index.reverse_entry (index : Index)
    (i : Fin index.reverse.depth) :
    index.reverse.entry i =
      index.entry (Fin.rev (Fin.castOrderIso index.reverse_depth i)) := by
  rcases index with ⟨n, composition⟩
  apply PNat.eq
  exact composition_blocksFun_reverse composition i

/-- The reciprocal-product summand in the increasing convention.
This is the convention in arXiv:2304.08722 and arXiv:2608.10675. -/
noncomputable def increasingSummand (index : Index)
    (m : StrictIncreasingTuple index.depth) : ℝ :=
  (∏ i : Fin index.depth, ((m.1 i : ℕ) : ℝ) ^ (index.entry i : ℕ))⁻¹

/-- The multiple-zeta series in the increasing convention.
This is the convention in arXiv:2304.08722 and arXiv:2608.10675. -/
@[nolint unusedArguments]
noncomputable def increasingValue (index : Index)
    (_h : index.IsIncreasingAdmissible) : ℝ :=
  ∑' m : StrictIncreasingTuple index.depth, increasingSummand index m

/-- Reversing coordinates identifies increasing tuples for an index with
decreasing tuples for its reversed index. -/
def increasingEquivDecreasing (index : Index) :
    StrictIncreasingTuple index.depth ≃
      StrictDecreasingTuple index.reverse.depth where
  toFun m :=
    ⟨fun i => m.1 (Fin.rev (Fin.castOrderIso index.reverse_depth i)), by
      intro i j hij
      have hcast :
          Fin.castOrderIso index.reverse_depth i <
            Fin.castOrderIso index.reverse_depth j := by
        simpa using hij
      exact m.2 (Fin.rev_lt_rev.mpr hcast)⟩
  invFun m :=
    ⟨fun i => m.1 (Fin.castOrderIso index.reverse_depth.symm (Fin.rev i)), by
      intro i j hij
      have hcast :
          Fin.castOrderIso index.reverse_depth.symm (Fin.rev j) <
            Fin.castOrderIso index.reverse_depth.symm (Fin.rev i) := by
        simpa using Fin.rev_lt_rev.mpr hij
      exact m.2 hcast⟩
  left_inv m := by
    ext i
    simp
  right_inv m := by
    ext i
    simp

@[simp]
theorem increasingEquivDecreasing_apply (index : Index)
    (m : StrictIncreasingTuple index.depth)
    (i : Fin index.reverse.depth) :
    (increasingEquivDecreasing index m).1 i =
      m.1 (Fin.rev (Fin.castOrderIso index.reverse_depth i)) :=
  rfl

/-- Reversing the tuple and exponent index preserves each reciprocal-product
summand. -/
theorem increasingSummand_eq_strictSummand_reverse (index : Index)
    (m : StrictIncreasingTuple index.depth) :
    increasingSummand index m =
      strictSummand index.reverse (increasingEquivDecreasing index m) := by
  unfold increasingSummand strictSummand
  let e : Fin index.reverse.depth ≃ Fin index.depth :=
    (Fin.castOrderIso index.reverse_depth).toEquiv.trans Fin.revPerm
  have hprod :
      (∏ i : Fin index.depth, ((m.1 i : ℝ) ^ (index.entry i : ℕ))) =
        ∏ j : Fin index.reverse.depth,
          ((m.1 (e j) : ℝ) ^ (index.reverse.entry j : ℕ)) := by
    symm
    apply Fintype.prod_equiv e
    intro j
    simp [e, Index.reverse_entry]
  rw [hprod]
  rfl

/-- The increasing and decreasing multiple-zeta series agree after reversing
the exponent index. -/
theorem increasingValue_eq_strictValue_reverse (index : Index)
    (h : index.IsIncreasingAdmissible) :
    increasingValue index h =
      strictValue index.reverse
        (Or.inl (index.isIncreasingAdmissible_iff_reverse_isAdmissible.mp h)) := by
  unfold increasingValue strictValue
  rw [show (fun m : StrictIncreasingTuple index.depth =>
      increasingSummand index m) =
      fun m => strictSummand index.reverse
        (increasingEquivDecreasing index m) by
    funext m
    exact increasingSummand_eq_strictSummand_reverse index m]
  exact Equiv.tsum_eq (increasingEquivDecreasing index)
    (strictSummand index.reverse)

end MetaMathlibExt.MultipleZeta
