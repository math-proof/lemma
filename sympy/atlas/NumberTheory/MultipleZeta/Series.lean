/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Series.lean -/

import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Ring.Real
import sympy.atlas.NumberTheory.MultipleZeta.Index
/-!
# Multiple-zeta and multiple-zeta-star series

This file defines multiple-zeta summands and values using strictly decreasing positive summation
variables, and multiple-zeta-star summands and values using weakly decreasing positive summation
variables. The star convention follows arXiv:2307.09867 and arXiv:2309.07569.
-/

namespace MetaMathlibExt.MultipleZeta

/-- The empty multiple-zeta index. Source: arXiv:2307.09867, empty-index convention. -/
def Index.empty : Index :=
  ⟨0, ⟨[], by simp, by simp⟩⟩

@[simp]
theorem Index.empty_entries : Index.empty.entries = [] :=
  rfl

@[simp]
theorem Index.empty_weight : Index.empty.weight = 0 :=
  rfl

@[simp]
theorem Index.empty_depth : Index.empty.depth = 0 :=
  rfl

/-- The `i`th entry of a multiple-zeta index, bundled as a positive natural number. -/
def Index.entry : (index : Index) → Fin index.depth → PNat
  | ⟨_, composition⟩ => fun i =>
    ⟨composition.blocksFun i, composition.blocks_pos (composition.blocksFun_mem_blocks i)⟩

@[simp]
theorem Index.entry_coe (index : Index) (i : Fin index.depth) :
    (index.entry i : ℕ) = index.2.blocksFun i :=
  rfl

/-- Strictly decreasing tuples `m₀ > m₁ > ⋯` of positive natural numbers.
Source: arXiv:2307.09867, lines 60–63, and arXiv:2309.07569, lines 76–80. -/
abbrev StrictDecreasingTuple (depth : ℕ) :=
  {m : Fin depth → PNat // StrictAnti m}

/-- The unique strictly decreasing tuple of length zero. -/
def StrictDecreasingTuple.empty : StrictDecreasingTuple 0 :=
  ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩

theorem StrictDecreasingTuple.eq_empty (m : StrictDecreasingTuple 0) :
    m = StrictDecreasingTuple.empty := by
  apply Subtype.ext
  funext i
  exact Fin.elim0 i

/-- The reciprocal product `(∏ i, mᵢ ^ kᵢ)⁻¹` attached to a decreasing tuple `m`.
Source: arXiv:2307.09867, lines 60–63, and arXiv:2309.07569, lines 76–80. -/
noncomputable def strictSummand (index : Index)
    (m : StrictDecreasingTuple index.depth) : ℝ :=
  (∏ i : Fin index.depth, ((m.1 i : ℕ) : ℝ) ^ (index.entry i : ℕ))⁻¹

@[simp]
theorem strictSummand_empty (m : StrictDecreasingTuple Index.empty.depth) :
    strictSummand Index.empty m = 1 := by
  unfold strictSummand
  have hempty : (Finset.univ : Finset (Fin Index.empty.depth)) = ∅ := by
    ext i
    exact Fin.elim0 (Index.empty_depth ▸ i)
  rw [hempty]
  simp only [Finset.prod_empty, inv_one]

/-- An index on which the ordinary strict multiple-zeta value is defined: either admissible or the
empty index. -/
def Index.IsAdmissibleOrEmpty (index : Index) : Prop :=
  index.IsAdmissible ∨ index.depth = 0

/-- The ordinary strict multiple-zeta series over decreasing tuples.
Source: arXiv:2307.09867, lines 60–63, and arXiv:2309.07569, lines 76–80. -/
@[nolint unusedArguments]
noncomputable def strictValue (index : Index) (_h : index.IsAdmissibleOrEmpty) : ℝ :=
  ∑' m : StrictDecreasingTuple index.depth, strictSummand index m

@[simp]
theorem strictValue_empty (h : Index.empty.IsAdmissibleOrEmpty) :
    strictValue Index.empty h = 1 := by
  let m : StrictDecreasingTuple Index.empty.depth := by
    simpa only [Index.empty_depth] using StrictDecreasingTuple.empty
  unfold strictValue
  rw [tsum_eq_single m]
  · exact strictSummand_empty m
  · intro b hb
    exfalso
    apply hb
    apply Subtype.ext
    funext i
    exact Fin.elim0 (Index.empty_depth ▸ i)

/-- Weakly decreasing tuples `m₀ ≥ m₁ ≥ ⋯` of positive natural numbers.
Source: arXiv:2307.09867, lines 61–65, and arXiv:2309.07569v2, lines 84–87. -/
abbrev WeaklyDecreasingTuple (depth : ℕ) :=
  {m : Fin depth → PNat // Antitone m}

/-- The unique weakly decreasing tuple of length zero. -/
def WeaklyDecreasingTuple.empty : WeaklyDecreasingTuple 0 :=
  ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩

theorem WeaklyDecreasingTuple.eq_empty (m : WeaklyDecreasingTuple 0) :
    m = WeaklyDecreasingTuple.empty := by
  apply Subtype.ext
  funext i
  exact Fin.elim0 i

/-- Every strictly decreasing tuple is weakly decreasing. -/
def StrictDecreasingTuple.toWeaklyDecreasing {depth : ℕ}
    (m : StrictDecreasingTuple depth) : WeaklyDecreasingTuple depth :=
  ⟨m.1, m.2.antitone⟩

/-- The reciprocal product `(∏ i, mᵢ ^ kᵢ)⁻¹` attached to a weakly decreasing tuple `m`.
Source: arXiv:2307.09867, lines 61–65, and arXiv:2309.07569v2, lines 84–87. -/
noncomputable def starSummand (index : Index)
    (m : WeaklyDecreasingTuple index.depth) : ℝ :=
  (∏ i : Fin index.depth, ((m.1 i : ℕ) : ℝ) ^ (index.entry i : ℕ))⁻¹

/-- Passing a strict tuple to the star summand recovers the strict summand. -/
@[simp]
theorem starSummand_toWeaklyDecreasing
    (index : Index) (m : StrictDecreasingTuple index.depth) :
    starSummand index m.toWeaklyDecreasing = strictSummand index m :=
  rfl

@[simp]
theorem starSummand_empty (m : WeaklyDecreasingTuple Index.empty.depth) :
    starSummand Index.empty m = 1 := by
  unfold starSummand
  have hempty : (Finset.univ : Finset (Fin Index.empty.depth)) = ∅ := by
    ext i
    exact Fin.elim0 (Index.empty_depth ▸ i)
  rw [hempty]
  simp only [Finset.prod_empty, inv_one]

/-- The multiple-zeta-star series over weakly decreasing tuples.
Source: arXiv:2307.09867, lines 61–65, and arXiv:2309.07569v2, lines 84–87. -/
@[nolint unusedArguments]
noncomputable def starValue (index : Index) (_h : index.IsAdmissibleOrEmpty) : ℝ :=
  ∑' m : WeaklyDecreasingTuple index.depth, starSummand index m

/-- The multiple-zeta-star value of the empty index is one.
Source: arXiv:2307.09867, lines 166–167. -/
@[simp]
theorem starValue_empty (h : Index.empty.IsAdmissibleOrEmpty) :
    starValue Index.empty h = 1 := by
  let m : WeaklyDecreasingTuple Index.empty.depth := by
    simpa only [Index.empty_depth] using WeaklyDecreasingTuple.empty
  unfold starValue
  rw [tsum_eq_single m]
  · exact starSummand_empty m
  · intro b hb
    exfalso
    apply hb
    apply Subtype.ext
    funext i
    exact Fin.elim0 (Index.empty_depth ▸ i)

end MetaMathlibExt.MultipleZeta
