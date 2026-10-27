import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Algebra.Lie.WittMultigradedDimension.Part11
open scoped BigOperators
open MetaMathlibExt


namespace MetaMathlibExt

/--
[wittAssocWord_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/WittMultigradedDimension.lean)
-/
@[path]
private lemma wittAssocWord_mul (K : Type) [Field K] {r : ℕ}
  (u v : List (Fin r)) :
  wittAssocWord K u * wittAssocWord K v = wittAssocWord K (u ++ v) := by
  rw [show wittAssocWord K u =
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid).symm
      (MonoidAlgebra.single (FreeMonoid.ofList u) 1) by rfl]
  rw [show wittAssocWord K v =
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid).symm
      (MonoidAlgebra.single (FreeMonoid.ofList v) 1) by rfl]
  rw [← map_mul, MonoidAlgebra.single_mul_single, one_mul]
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wittAssocWord_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/WittMultigradedDimension.lean)
-/
@[path]
private lemma wittAssocWord_singleton (K : Type) [Field K] {r : ℕ} (i : Fin r) :
  wittAssocWord K [i] = FreeAlgebra.ι K i := by
  rw [wittAssocWord, FreeMonoid.ofList_singleton]
  apply (FreeAlgebra.basisFreeMonoid K (Fin r)).repr.injective
  rw [Module.Basis.repr_self]
  ext w
  simp [FreeAlgebra.basisFreeMonoid, FreeAlgebra.equivMonoidAlgebraFreeMonoid]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wittWordContent_eq_length_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/WittMultigradedDimension.lean)
-/
@[path]
private lemma wittWordContent_eq_length_eq {r : ℕ} {u v : List (Fin r)}
  (h : wittWordContent u = wittWordContent v) : u.length = v.length := by
  rw [← sum_wittWordContent u, ← sum_wittWordContent v, h]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wittAssocWord_mem_spanGE](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/WittMultigradedDimension.lean)
-/
@[path]
private lemma wittAssocWord_mem_spanGE (K : Type) [Field K] {r : ℕ}
  (w : List (Fin r)) : wittAssocWord K w ∈ wittWordSpanGE K w := by
  apply Submodule.subset_span
  exact ⟨w, ⟨rfl, le_rfl⟩, rfl⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wittWordSpanGT_le_spanGE](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/WittMultigradedDimension.lean)
-/
@[path]
private lemma wittWordSpanGT_le_spanGE (K : Type) [Field K] {r : ℕ}
  (w : List (Fin r)) : wittWordSpanGT K w ≤ wittWordSpanGE K w := by
  apply Submodule.span_mono
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨z, ⟨hz.1, hz.2.le⟩, rfl⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[witt_mul_mem_wordSpan](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/WittMultigradedDimension.lean)
-/
@[path]
private lemma witt_mul_mem_wordSpan (K : Type) [Field K] {r : ℕ}
  {S T U : Set (List (Fin r))}
  (hmul : ∀ u ∈ S, ∀ v ∈ T, u ++ v ∈ U)
  {x y : FreeAlgebra K (Fin r)}
  (hx : x ∈ Submodule.span K (wittAssocWord K '' S))
  (hy : y ∈ Submodule.span K (wittAssocWord K '' T)) :
  x * y ∈ Submodule.span K (wittAssocWord K '' U) := by
  apply LinearMap.BilinMap.apply_apply_mem_of_mem_span
    (Submodule.span K (wittAssocWord K '' U))
    (wittAssocWord K '' S) (wittAssocWord K '' T) (LinearMap.mul K _)
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    change wittAssocWord K u * wittAssocWord K v ∈ _
    rw [wittAssocWord_mul]
    exact Submodule.subset_span ⟨u ++ v, hmul u hu v hv, rfl⟩
  · exact hx
  · exact hy

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wittWordSpanGE_le_spanGT_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/WittMultigradedDimension.lean)
-/
@[path]
private lemma wittWordSpanGE_le_spanGT_of_lt (K : Type) [Field K] {r : ℕ}
  {u v : List (Fin r)} (hcontent : wittWordContent v = wittWordContent u)
  (hlt : u < v) : wittWordSpanGE K v ≤ wittWordSpanGT K u := by
  apply Submodule.span_mono
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨z, ⟨hz.1.trans hcontent, hlt.trans_le hz.2⟩, rfl⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wittTriangular_mem_spanGE](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/WittMultigradedDimension.lean)
-/
@[path]
private lemma wittTriangular_mem_spanGE (K : Type) [Field K] {r : ℕ}
  {w : List (Fin r)} {x : FreeAlgebra K (Fin r)} (hx : WittTriangular K w x) :
  x ∈ wittWordSpanGE K w := by
  rw [← sub_add_cancel x (wittAssocWord K w)]
  exact Submodule.add_mem _ (wittWordSpanGT_le_spanGE K w hx)
    (wittAssocWord_mem_spanGE K w)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wittWordSpanGT_repr_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/WittMultigradedDimension.lean)
-/
@[path]
private lemma wittWordSpanGT_repr_eq_zero (K : Type) [Field K] {r : ℕ}
  {w q : List (Fin r)} {x : FreeAlgebra K (Fin r)} (hq : ¬w < q)
  (hx : x ∈ wittWordSpanGT K w) :
  (FreeAlgebra.basisFreeMonoid K (Fin r)).repr x (FreeMonoid.ofList q) = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    rw [wittAssocWord, Module.Basis.repr_self]
    apply Finsupp.single_eq_of_ne
    intro heq
    have hqz : q = z := FreeMonoid.ofList.injective heq
    exact hq (hqz ▸ hz.2)
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | smul c x _ hx => simp [map_smul, hx]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wittTriangular_repr_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/WittMultigradedDimension.lean)
-/
@[path]
private lemma wittTriangular_repr_self (K : Type) [Field K] {r : ℕ}
  {w : List (Fin r)} {x : FreeAlgebra K (Fin r)} (hx : WittTriangular K w x) :
  (FreeAlgebra.basisFreeMonoid K (Fin r)).repr x (FreeMonoid.ofList w) = 1 := by
  have hzero := wittWordSpanGT_repr_eq_zero K (w := w) (q := w) (lt_irrefl w) hx
  rw [map_sub, Finsupp.sub_apply] at hzero
  rw [wittAssocWord, Module.Basis.repr_self, Finsupp.single_eq_same] at hzero
  exact sub_eq_zero.mp hzero

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wittTriangular_repr_eq_zero_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/WittMultigradedDimension.lean)
-/
@[path]
private lemma wittTriangular_repr_eq_zero_of_lt (K : Type) [Field K] {r : ℕ}
  {w q : List (Fin r)} {x : FreeAlgebra K (Fin r)} (hx : WittTriangular K w x)
  (hqw : q < w) :
  (FreeAlgebra.basisFreeMonoid K (Fin r)).repr x (FreeMonoid.ofList q) = 0 := by
  have hzero := wittWordSpanGT_repr_eq_zero K (w := w) (q := q)
    (not_lt_of_ge hqw.le) hx
  rw [map_sub, Finsupp.sub_apply] at hzero
  have hne : FreeMonoid.ofList q ≠ FreeMonoid.ofList w := by
    exact fun heq => hqw.ne (FreeMonoid.ofList.injective heq)
  rwa [wittAssocWord, Module.Basis.repr_self, Finsupp.single_eq_of_ne hne, sub_zero] at hzero

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wittLyndonBracket_mem_spanFrom](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/WittMultigradedDimension.lean)
-/
@[path]
private lemma wittLyndonBracket_mem_spanFrom (K : Type) [Field K] {r : ℕ}
  {degree : Fin r → ℕ} {lower w : List (Fin r)} (hw : IsLyndonWord w)
  (hdegree : wittWordContent w = degree) (hlower : lower ≤ w) :
  wittLyndonBracket K w hw ∈ wittLyndonSpanFrom K degree lower := by
  apply Submodule.subset_span
  exact ⟨w, hw, hdegree, hlower, rfl⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wittLyndonSpanFrom_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/WittMultigradedDimension.lean)
-/
@[path]
private lemma wittLyndonSpanFrom_mono (K : Type) [Field K] {r : ℕ}
  {degree : Fin r → ℕ} {u v : List (Fin r)} (huv : u ≤ v) :
  wittLyndonSpanFrom K degree v ≤ wittLyndonSpanFrom K degree u := by
  apply Submodule.span_mono
  rintro x ⟨w, hw, hdegree, hvw, rfl⟩
  exact ⟨w, hw, hdegree, huv.trans hvw, rfl⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wittLyndonPairRel_wellFounded](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/WittMultigradedDimension.lean)
-/
@[path]
private lemma wittLyndonPairRel_wellFounded {r n : ℕ} :
  WellFounded (@WittLyndonPairRel r n) :=
  Finite.wellFounded_of_trans_of_irrefl _

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wittContent_append_replace](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/WittMultigradedDimension.lean)
-/
@[path]
private lemma wittContent_append_replace {r : ℕ} {a x y : List (Fin r)}
  (h : wittWordContent x = wittWordContent y) :
  wittWordContent (a ++ x) = wittWordContent (a ++ y) := by
  rw [wittWordContent_append, wittWordContent_append, h]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wittContent_swap_append](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/WittMultigradedDimension.lean)
-/
@[path]
private lemma wittContent_swap_append {r : ℕ} (u v : List (Fin r)) :
  wittWordContent (u ++ v) = wittWordContent (v ++ u) := by
  rw [wittWordContent_append, wittWordContent_append]
  funext i
  exact Nat.add_comm _ _

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wittNil_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/WittMultigradedDimension.lean)
-/
@[path]
private lemma wittNil_le {α : Type*} [LinearOrder α] (w : List α) : [] ≤ w := by
  obtain h | h := List.lex_nil_or_eq_nil (r := fun a b : α => a < b) w
  · apply le_of_lt
    exact h
  · exact h ▸ le_rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wittLyndonSpan_eq_span_range](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/WittMultigradedDimension.lean)
-/
@[path]
private lemma wittLyndonSpan_eq_span_range (K : Type) [Field K] {r : ℕ}
  (degree : Fin r → ℕ) :
  wittLyndonSpanFrom K degree [] =
    Submodule.span K (Set.range (wittLyndonFamily K degree)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨w, hw, hdegree, _, rfl⟩
    apply Submodule.subset_span
    refine ⟨⟨⟨w, hdegree⟩, hw⟩, ?_⟩
    rfl
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    exact wittLyndonBracket_mem_spanFrom K w.2 w.1.2 (wittNil_le w.1.1)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[witt_multigraded_dimension_formula](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/WittMultigradedDimension.lean)
-/
@[path]
lemma witt_multigraded_dimension_formula
  [Field K]
  {r : ℕ}
  {degree : Fin r → ℕ}
-- given
  (hr : 0 < r)
  (hdegree : 0 < ∑ i, degree i) :
-- imply
  (Module.finrank K (freeLieMultihomogeneousComponent K degree) : ℚ) =
    wittMultigradedValue degree :=
-- proof
  finrank_freeLieMultihomogeneousComponent K degree hdegree

end MetaMathlibExt

/--
[finrank_freeLieMultihomogeneousComponent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/WittMultigradedDimension.lean)
-/
@[path]
private lemma finrank_freeLieMultihomogeneousComponent_eq
  [Field K]
  {r : ℕ}
  {degree : Fin r → ℕ}
-- given
  (hdegree : 0 < ∑ i, degree i) :
-- imply
  (Module.finrank K (freeLieMultihomogeneousComponent K degree) : ℚ) =
    wittMultigradedValue degree := by
-- proof
  apply MetaMathlibExt.finrank_freeLieMultihomogeneousComponent K degree hdegree


-- created on 2026-10-20
-- updated on 2026-10-26
