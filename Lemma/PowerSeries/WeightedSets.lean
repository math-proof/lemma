import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet WeightedSetExamples DominoTilingsZ


/--
[weight_gen_fun_eq_sum_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma weight_gen_fun_eq_sum_eq
  [CommSemiring R]
-- given
  {α : Type*}
  (W : WeightedSet α)
  (hft : W.IsFiniteType) :
-- imply
  W.weightGenFun (R := R) hft = PowerSeries.mk fun n => ((hft n).toFinset.card : R) := by
-- proof
  apply WeightedSet.weightGenFun_eq_sum W hft

/--
[weight_gen_fun_eq_of_isomorphic_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma weight_gen_fun_eq_of_isomorphic_eq
  [CommSemiring R]
-- given
  {α β : Type*}
  (W₁ : WeightedSet α)
  (W₂ : WeightedSet β)
  (hft₁ : W₁.IsFiniteType)
  (hft₂ : W₂.IsFiniteType)
  (h : AreIsomorphic W₁ W₂) :
-- imply
  W₁.weightGenFun (R := R) hft₁ = W₂.weightGenFun hft₂ := by
-- proof
  apply WeightedSet.weightGenFun_eq_of_isomorphic W₁ W₂ hft₁ hft₂ h

/--
[disjoint_union_is_finite_type_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma disjoint_union_is_finite_type_is
-- given
  {α β : Type*}
  (W₁ : WeightedSet α)
  (W₂ : WeightedSet β)
  (hft₁ : W₁.IsFiniteType)
  (hft₂ : W₂.IsFiniteType) :
-- imply
  (disjointUnion W₁ W₂).IsFiniteType := by
-- proof
  apply WeightedSet.disjointUnion_isFiniteType W₁ W₂ hft₁ hft₂

/--
[weight_gen_fun_disjoint_union_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma weight_gen_fun_disjoint_union_eq
  [CommSemiring R]
-- given
  {α β : Type*}
  (W₁ : WeightedSet α)
  (W₂ : WeightedSet β)
  (hft₁ : W₁.IsFiniteType)
  (hft₂ : W₂.IsFiniteType) :
-- imply
  (disjointUnion W₁ W₂).weightGenFun (R := R) (disjointUnion_isFiniteType W₁ W₂ hft₁ hft₂) =
    W₁.weightGenFun hft₁ + W₂.weightGenFun hft₂ := by
-- proof
  apply WeightedSet.weightGenFun_disjointUnion W₁ W₂ hft₁ hft₂

/--
[prod_is_finite_type_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma prod_is_finite_type_is
-- given
  {α β : Type*}
  (W₁ : WeightedSet α)
  (W₂ : WeightedSet β)
  (hft₁ : W₁.IsFiniteType)
  (hft₂ : W₂.IsFiniteType) :
-- imply
  (prod W₁ W₂).IsFiniteType := by
-- proof
  apply WeightedSet.prod_isFiniteType W₁ W₂ hft₁ hft₂

/--
[weight_gen_fun_prod_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma weight_gen_fun_prod_eq
  [CommSemiring R]
-- given
  {α β : Type*} [DecidableEq α] [DecidableEq β]
  (W₁ : WeightedSet α)
  (W₂ : WeightedSet β)
  (hft₁ : W₁.IsFiniteType)
  (hft₂ : W₂.IsFiniteType) :
-- imply
  (prod W₁ W₂).weightGenFun (R := R) (prod_isFiniteType W₁ W₂ hft₁ hft₂) =
    W₁.weightGenFun hft₁ * W₂.weightGenFun hft₂ := by
-- proof
  apply WeightedSet.weightGenFun_prod W₁ W₂ hft₁ hft₂

/--
[pow_is_finite_type_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma pow_is_finite_type_is
-- given
  {α : Type*}
  (W : WeightedSet α)
  (hft : W.IsFiniteType)
  (k : ℕ) :
-- imply
  (W.pow k).IsFiniteType := by
-- proof
  apply WeightedSet.pow_isFiniteType W hft k

/--
[weight_gen_fun_pow_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma weight_gen_fun_pow_eq
  [CommSemiring R]
-- given
  {α : Type*}
  (W : WeightedSet α)
  (hft : W.IsFiniteType)
  (k : ℕ) :
-- imply
  (W.pow k).weightGenFun (R := R) (pow_isFiniteType W hft k) =
    (W.weightGenFun hft) ^ k := by
-- proof
  apply WeightedSet.weightGenFun_pow W hft k

/--
[tuples_weight_eq_pow_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma tuples_weight_eq_pow_eq
-- given
  {α : Type*}
  (W : WeightedSet α)
  (n : ℕ)
  (f : Fin n → α) :
-- imply
  W.tuples.weight ⟨n, f⟩ = (W.pow n).weight f := by
-- proof
  apply WeightedSet.tuples_weight_eq_pow W n f

/--
[tuples_is_finite_type_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma tuples_is_finite_type_is
-- given
  {α : Type*}
  (W : WeightedSet α)
  (hpos : W.HasPositiveWeights)
  (hft : W.IsFiniteType) :
-- imply
  W.tuples.IsFiniteType := by
-- proof
  apply WeightedSet.tuples_isFiniteType W hft hpos

/--
[binary_strings_is_finite_type_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma binary_strings_is_finite_type_is :
-- imply
  BinaryStrings.IsFiniteType := by
-- proof
  apply WeightedSetExamples.binaryStrings_isFiniteType

/--
[weight_gen_fun_binary_strings_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma weight_gen_fun_binary_strings_eq :
-- imply
  BinaryStrings.weightGenFun (R := ℚ) binaryStrings_isFiniteType =
    PowerSeries.mk fun n => (2 ^ n : ℚ) := by
-- proof
  apply WeightedSetExamples.weightGenFun_binaryStrings

/--
[positive_integers_is_finite_type_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma positive_integers_is_finite_type_is :
-- imply
  PositiveIntegers.IsFiniteType := by
-- proof
  apply WeightedSetExamples.positiveIntegers_isFiniteType

/--
[weight_gen_fun_positive_integers_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma weight_gen_fun_positive_integers_eq :
-- imply
  PositiveIntegers.weightGenFun (R := ℚ) positiveIntegers_isFiniteType =
    PowerSeries.X * (PowerSeries.invOneSubPow ℚ 1).val := by
-- proof
  apply WeightedSetExamples.weightGenFun_positiveIntegers

/--
[compositions_is_finite_type_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma compositions_is_finite_type_is
-- given
  (k : ℕ) :
-- imply
  (Compositions k).IsFiniteType := by
-- proof
  apply WeightedSetExamples.compositions_isFiniteType k

/--
[weight_gen_fun_compositions_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma weight_gen_fun_compositions_eq
-- given
  (k : ℕ) :
-- imply
  (Compositions k).weightGenFun (R := ℚ) (compositions_isFiniteType k) =
    (PowerSeries.X * (PowerSeries.invOneSubPow ℚ 1).val) ^ k := by
-- proof
  apply WeightedSetExamples.weightGenFun_compositions k

/--
[mem_rectangle_iff](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma mem_rectangle_iff
-- given
  {n m : ℕ}
  {p : ℤ × ℤ} :
-- imply
  p ∈ Rectangle n m ↔ 1 ≤ p.1 ∧ p.1 ≤ n ∧ 1 ≤ p.2 ∧ p.2 ≤ m := by
-- proof
  apply DominoTilingsZ.mem_rectangle_iff

/--
[rectangle_zero_left_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma rectangle_zero_left_eq
-- given
  (m : ℕ) :
-- imply
  Rectangle 0 m = ∅ := by
-- proof
  apply DominoTilingsZ.Rectangle_zero_left m

/--
[rectangle_zero_right_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma rectangle_zero_right_eq
-- given
  (n : ℕ) :
-- imply
  Rectangle n 0 = ∅ := by
-- proof
  apply DominoTilingsZ.Rectangle_zero_right n

/--
[rectangle_ncard_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma rectangle_ncard_eq
-- given
  (n m : ℕ) :
-- imply
  (Rectangle n m).ncard = n * m := by
-- proof
  apply DominoTilingsZ.Rectangle_ncard n m

/--
[domino_to_shape_ncard_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma domino_to_shape_ncard_eq
-- given
  (d : Domino) :
-- imply
  d.toShape.ncard = 2 := by
-- proof
  apply DominoTilingsZ.Domino.toShape_ncard d

/--
[domino_horizontal_to_shape_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma domino_horizontal_to_shape_eq
-- given
  (i j : ℤ) :
-- imply
  (Domino.horizontal i j).toShape = {(i, j), (i + 1, j)} := by
-- proof
  apply DominoTilingsZ.Domino.horizontal_toShape i j

/--
[domino_vertical_to_shape_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma domino_vertical_to_shape_eq
-- given
  (i j : ℤ) :
-- imply
  (Domino.vertical i j).toShape = {(i, j), (i, j + 1)} := by
-- proof
  apply DominoTilingsZ.Domino.vertical_toShape i j

/--
[domino_to_shape_nonempty_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma domino_to_shape_nonempty_is
-- given
  (d : Domino) :
-- imply
  d.toShape.Nonempty := by
-- proof
  apply DominoTilingsZ.Domino.toShape_nonempty d

/--
[domino_to_shape_finite_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma domino_to_shape_finite_is
-- given
  (d : Domino) :
-- imply
  d.toShape.Finite := by
-- proof
  apply DominoTilingsZ.Domino.toShape_finite d

/--
[domino_eq_of_to_shape_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma domino_eq_of_to_shape_eq
-- given
  {d1 d2 : Domino}
  (h : d1.toShape = d2.toShape) :
-- imply
  d1 = d2 := by
-- proof
  apply DominoTilingsZ.Domino.eq_of_toShape_eq h

/--
[tiling_ext_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma tiling_ext_eq
-- given
  {S : Shape}
  (T1 T2 : Tiling S)
  (h : T1.dominos = T2.dominos) :
-- imply
  T1 = T2 := by
-- proof
  apply DominoTilingsZ.Tiling.ext T1 T2 h

/--
[tiling_unique_empty_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma tiling_unique_empty_eq
-- given
  (T : Tiling (∅ : Shape)) :
-- imply
  T.dominos = ∅ := by
-- proof
  apply DominoTilingsZ.Tiling.unique_empty T

/--
[tilings_height2_is_finite_type_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma tilings_height2_is_finite_type_is :
-- imply
  TilingsHeight2.IsFiniteType := by
-- proof
  apply DominoTilingsZ.tilingsHeight2_isFiniteType

/--
[has_fault_eq_of_dominos_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma has_fault_eq_of_dominos_eq
-- given
  {n : ℕ}
  {T1 T2 : Tiling (Rectangle n 2)}
  (h : T1.dominos = T2.dominos)
  (k : ℕ) :
-- imply
  hasFault n T1 k ↔ hasFault n T2 k := by
-- proof
  apply DominoTilingsZ.hasFault_eq_of_dominos_eq h k

/--
[is_faultfree_eq_of_dominos_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma is_faultfree_eq_of_dominos_eq
-- given
  {n : ℕ}
  {T1 T2 : Tiling (Rectangle n 2)}
  (h : T1.dominos = T2.dominos) :
-- imply
  isFaultfree n T1 ↔ isFaultfree n T2 := by
-- proof
  apply DominoTilingsZ.isFaultfree_eq_of_dominos_eq h

/--
[faultfree_tilings_height2_is_finite_type_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma faultfree_tilings_height2_is_finite_type_is :
-- imply
  FaultfreeTilingsHeight2.IsFiniteType := by
-- proof
  apply DominoTilingsZ.faultfreeTilingsHeight2_isFiniteType

/--
[exists_domino_covering_11_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma exists_domino_covering_11_is
-- given
  (n : ℕ)
  (hn : n ≥ 1)
  (T : Tiling (Rectangle n 2)) :
-- imply
  ∃ d ∈ T.dominos, (1, 1) ∈ d.toShape := by
-- proof
  apply DominoTilingsZ.exists_domino_covering_11 n hn T

/--
[domino_covering_11_valid_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma domino_covering_11_valid_eq
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (d : Domino)
  (hd : d ∈ T.dominos)
  (h : (1, 1) ∈ d.toShape) :
-- imply
  d = .vertical 1 1 ∨ d = .horizontal 1 1 := by
-- proof
  apply DominoTilingsZ.domino_covering_11_valid n T d hd h

/--
[fault_at_1_if_vertical_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma fault_at_1_if_vertical_is
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (hn : n ≥ 2)
  (hv : Domino.vertical 1 1 ∈ T.dominos) :
-- imply
  hasFault n T 1 := by
-- proof
  apply DominoTilingsZ.fault_at_1_if_vertical n hn T hv

/--
[horizontal_12_if_horizontal_11_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma horizontal_12_if_horizontal_11_is
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (hn : n ≥ 1)
  (hh : Domino.horizontal 1 1 ∈ T.dominos) :
-- imply
  Domino.horizontal 1 2 ∈ T.dominos := by
-- proof
  apply DominoTilingsZ.horizontal_12_if_horizontal_11 n hn T hh

/--
[fault_at_2_if_horizontal_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma fault_at_2_if_horizontal_is
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (hn : n ≥ 3)
  (hh : Domino.horizontal 1 1 ∈ T.dominos) :
-- imply
  hasFault n T 2 := by
-- proof
  apply DominoTilingsZ.fault_at_2_if_horizontal n hn T hh

/--
[faultfree_height2_classification_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma faultfree_height2_classification_eq
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (hff : isFaultfree n T) :
-- imply
  n = 1 ∨ n = 2 := by
-- proof
  apply DominoTilingsZ.faultfree_height2_classification n T hff

/--
[tiling_1_2_faultfree_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma tiling_1_2_faultfree_is :
-- imply
  isFaultfree 1 tiling_1_2 := by
-- proof
  apply DominoTilingsZ.tiling_1_2_faultfree

/--
[tiling_1_2_unique_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma tiling_1_2_unique_eq
-- given
  (T : Tiling (Rectangle 1 2)) :
-- imply
  T = tiling_1_2 := by
-- proof
  apply DominoTilingsZ.tiling_1_2_unique T

/--
[faultfree_tilings_height2_weight1_unique_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma faultfree_tilings_height2_weight1_unique_eq
-- given
  (x : Σ n : ℕ, Subtype (fun (T : Tiling (Rectangle n 2)) => isFaultfree n T))
  (hx : FaultfreeTilingsHeight2.weight x = 1) :
-- imply
  x = ⟨1, faultfreeTiling_1_2⟩ := by
-- proof
  apply DominoTilingsZ.faultfreeTilingsHeight2_weight1_unique x hx

/--
[count_of_weight_faultfree_height2_one_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma count_of_weight_faultfree_height2_one_eq :
-- imply
  FaultfreeTilingsHeight2.countOfWeight faultfreeTilingsHeight2_isFiniteType 1 = 1 := by
-- proof
  apply DominoTilingsZ.countOfWeight_faultfreeHeight2_one

/--
[two_horizontal_dominos_is_faultfree_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma two_horizontal_dominos_is_faultfree_is :
-- imply
  isFaultfree 2 twoHorizontalDominos := by
-- proof
  apply DominoTilingsZ.twoHorizontalDominos_isFaultfree

/--
[faultfree_tiling_width2_unique_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma faultfree_tiling_width2_unique_eq
-- given
  (T : Tiling (Rectangle 2 2))
  (hff : isFaultfree 2 T) :
-- imply
  T = twoHorizontalDominos := by
-- proof
  apply DominoTilingsZ.faultfree_tiling_width2_unique T hff

/--
[count_of_weight_faultfree_height2_two_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma count_of_weight_faultfree_height2_two_eq :
-- imply
  FaultfreeTilingsHeight2.countOfWeight faultfreeTilingsHeight2_isFiniteType 2 = 1 := by
-- proof
  apply DominoTilingsZ.countOfWeight_faultfreeHeight2_two

/--
[count_of_weight_faultfree_height2_eq_zero_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma count_of_weight_faultfree_height2_eq_zero_eq
-- given
  (n : ℕ)
  (hn1 : n ≠ 1)
  (hn2 : n ≠ 2) :
-- imply
  FaultfreeTilingsHeight2.countOfWeight faultfreeTilingsHeight2_isFiniteType n = 0 := by
-- proof
  apply DominoTilingsZ.countOfWeight_faultfreeHeight2_eq_zero n hn1 hn2

/--
[weight_gen_fun_faultfree_height2_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma weight_gen_fun_faultfree_height2_eq :
-- imply
  FaultfreeTilingsHeight2.weightGenFun (R := ℚ) faultfreeTilingsHeight2_isFiniteType =
    PowerSeries.X + PowerSeries.X ^ 2 := by
-- proof
  apply DominoTilingsZ.weightGenFun_faultfreeHeight2

/--
[domino_shift_to_shape_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma domino_shift_to_shape_eq
-- given
  (d : Domino)
  (offset : ℤ) :
-- imply
  (d.shift offset).toShape = d.toShape.image (fun p => (p.1 + offset, p.2)) := by
-- proof
  apply DominoTilingsZ.Domino.shift_toShape d offset

/--
[domino_shift_injective_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma domino_shift_injective_is
-- given
  (offset : ℤ) :
-- imply
  Function.Injective (fun d : Domino => d.shift offset) := by
-- proof
  apply DominoTilingsZ.Domino.shift_injective offset

/--
[domino_shift_zero_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma domino_shift_zero_eq
-- given
  (d : Domino) :
-- imply
  d.shift 0 = d := by
-- proof
  apply DominoTilingsZ.Domino.shift_zero d

/--
[domino_shift_shift_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma domino_shift_shift_eq
-- given
  (d : Domino)
  (a b : ℤ) :
-- imply
  (d.shift a).shift b = d.shift (a + b) := by
-- proof
  apply DominoTilingsZ.Domino.shift_shift d a b

/--
[rectangle_shift_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma rectangle_shift_eq
-- given
  (n m : ℕ)
  (offset : ℤ) :
-- imply
  (Rectangle n m).image (fun p => (p.1 + offset, p.2)) =
      {p : ℤ × ℤ | 1 + offset ≤ p.1 ∧ p.1 ≤ n + offset ∧ 1 ≤ p.2 ∧ p.2 ≤ m} := by
-- proof
  apply DominoTilingsZ.Rectangle_shift n m offset

/--
[tiling_cast_dominos_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma tiling_cast_dominos_eq
-- given
  {S S' : Shape}
  (h : S = S')
  (T : Tiling S) :
-- imply
  (T.cast h).dominos = T.dominos := by
-- proof
  apply DominoTilingsZ.Tiling.cast_dominos h T

/--
[tiling_subst_dominos_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma tiling_subst_dominos_eq
-- given
  {n m : ℕ}
  (h : n = m)
  (T : Tiling (Rectangle n 2)) :
-- imply
  (h ▸ T).dominos = T.dominos := by
-- proof
  apply DominoTilingsZ.Tiling.subst_dominos h T

/--
[partial_width_sum_zero_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma partial_width_sum_zero_eq
-- given
  (k : ℕ)
  (i : Fin k)
  (hi : i.val = 0)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T'))) :
-- imply
  partialWidthSum k ts i = 0 := by
-- proof
  apply DominoTilingsZ.partialWidthSum_zero k ts i hi

/--
[domino_shift_nat_zero_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma domino_shift_nat_zero_eq
-- given
  (d : Domino) :
-- imply
  d.shiftNat 0 = d := by
-- proof
  apply DominoTilingsZ.Domino.shiftNat_zero d

/--
[domino_shift_nat_to_shape_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma domino_shift_nat_to_shape_eq
-- given
  (d : Domino)
  (offset : ℕ) :
-- imply
  (d.shiftNat offset).toShape = d.toShape.image (fun p => (p.1 + (offset : ℤ), p.2)) := by
-- proof
  apply DominoTilingsZ.Domino.shiftNat_toShape d offset

/--
[domino_shift_nat_shift_nat_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma domino_shift_nat_shift_nat_eq
-- given
  (d : Domino)
  (a b : ℕ) :
-- imply
  (d.shiftNat a).shiftNat b = d.shiftNat (a + b) := by
-- proof
  apply DominoTilingsZ.Domino.shiftNat_shiftNat d a b

/--
[compose_tilings_component_dominos_disjoint_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma compose_tilings_component_dominos_disjoint_is
-- given
  (k : ℕ)
  (i1 i2 : Fin k)
  (d1 d2 : Domino)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T')))
  (hi : i1 ≠ i2)
  (hd1 : d1 ∈ composeTilings_component_dominos k ts i1)
  (hd2 : d2 ∈ composeTilings_component_dominos k ts i2) :
-- imply
  Disjoint d1.toShape d2.toShape := by
-- proof
  apply DominoTilingsZ.composeTilings_component_dominos_disjoint k ts i1 i2 hi d1 hd1 d2 hd2

/--
[compose_tilings_dominos_one_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma compose_tilings_dominos_one_eq
-- given
  (ts : Fin 1 → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T'))) :
-- imply
  composeTilings_dominos 1 ts = (ts 0).2.val.dominos := by
-- proof
  apply DominoTilingsZ.composeTilings_dominos_one ts

/--
[compose_tilings_one_dominos_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma compose_tilings_one_dominos_eq
-- given
  (ts : Fin 1 → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T'))) :
-- imply
  (composeTilings 1 ts).2.dominos = (ts 0).2.val.dominos := by
-- proof
  apply DominoTilingsZ.composeTilings_one_dominos ts

/--
[compose_tilings_one_width_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma compose_tilings_one_width_eq
-- given
  (ts : Fin 1 → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T'))) :
-- imply
  (composeTilings 1 ts).1 = (ts 0).1 := by
-- proof
  apply DominoTilingsZ.composeTilings_one_width ts

/--
[compose_tilings_one_tiling_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma compose_tilings_one_tiling_eq
-- given
  (ts : Fin 1 → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T'))) :
-- imply
  (composeTilings 1 ts).2 = (ts 0).2.val := by
-- proof
  apply DominoTilingsZ.composeTilings_one_tiling ts

/--
[compose_tilings_one_is_faultfree_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma compose_tilings_one_is_faultfree_is
-- given
  (ts : Fin 1 → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T'))) :
-- imply
  isFaultfree (composeTilings 1 ts).1 (composeTilings 1 ts).2 := by
-- proof
  apply DominoTilingsZ.composeTilings_one_isFaultfree ts

/--
[compose_tilings_prepend_width_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma compose_tilings_prepend_width_eq
-- given
  (m first_width : ℕ)
  (first : Subtype (fun (T' : Tiling (Rectangle first_width 2)) => isFaultfree first_width T'))
  (rest : Fin m → (Σ w : ℕ, Subtype (fun (T' : Tiling (Rectangle w 2)) => isFaultfree w T')))
  (ts : Fin (m + 1) → (Σ w : ℕ, Subtype (fun (T' : Tiling (Rectangle w 2)) => isFaultfree w T')))
  (hts : ts = fun i => if hi : i.val = 0 then ⟨first_width, first⟩ else rest ⟨i.val - 1, by omega⟩) :
-- imply
  (composeTilings (m + 1) ts).1 = first_width + ∑ j : Fin m, (rest j).1 := by
-- proof
  apply DominoTilingsZ.composeTilings_prepend_width m first_width first rest ts hts

/--
[compose_tilings_prepend_width'_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma compose_tilings_prepend_width'_eq
-- given
  (m first_width rest_width : ℕ)
  (first : Subtype (fun (T' : Tiling (Rectangle first_width 2)) => isFaultfree first_width T'))
  (rest : Fin m → (Σ w : ℕ, Subtype (fun (T' : Tiling (Rectangle w 2)) => isFaultfree w T')))
  (ts : Fin (m + 1) → (Σ w : ℕ, Subtype (fun (T' : Tiling (Rectangle w 2)) => isFaultfree w T')))
  (hrest : (composeTilings m rest).1 = rest_width)
  (hts : ts = fun i => if hi : i.val = 0 then ⟨first_width, first⟩ else rest ⟨i.val - 1, by omega⟩) :
-- imply
  (composeTilings (m + 1) ts).1 = first_width + rest_width := by
-- proof
  apply DominoTilingsZ.composeTilings_prepend_width' m first_width rest_width first rest hrest ts hts

/--
[domino_shift_neg_to_shape_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma domino_shift_neg_to_shape_eq
-- given
  (d : Domino)
  (offset : ℕ) :
-- imply
  (d.shiftNeg offset).toShape = d.toShape.image (fun p => (p.1 - (offset : ℤ), p.2)) := by
-- proof
  apply DominoTilingsZ.Domino.shiftNeg_toShape d offset

/--
[domino_shift_neg_shift_nat_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma domino_shift_neg_shift_nat_eq
-- given
  (d : Domino)
  (k : ℕ) :
-- imply
  (d.shiftNat k).shiftNeg k = d := by
-- proof
  apply DominoTilingsZ.Domino.shiftNeg_shiftNat d k

/--
[domino_shift_nat_shift_neg_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma domino_shift_nat_shift_neg_eq
-- given
  (d : Domino)
  (k : ℕ) :
-- imply
  (d.shiftNeg k).shiftNat k = d := by
-- proof
  apply DominoTilingsZ.Domino.shiftNat_shiftNeg d k

/--
[domino_left_or_right_at_fault_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma domino_left_or_right_at_fault_is
-- given
  {n : ℕ}
  {T : Tiling (Rectangle n 2)}
  {k : ℕ}
  (d : Domino)
  (hk : hasFault n T k)
  (hd : d ∈ T.dominos) :
-- imply
  d.inLeftPart k ∨ d.inRightPart k := by
-- proof
  apply DominoTilingsZ.domino_left_or_right_at_fault hk d hd

/--
[restrict_tiling_left_proof_irrel_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma restrict_tiling_left_proof_irrel_eq
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (k : ℕ)
  (hk1 hk2 : hasFault n T k) :
-- imply
  restrictTilingLeft n T k hk1 = restrictTilingLeft n T k hk2 := by
-- proof
  apply DominoTilingsZ.restrictTilingLeft_proof_irrel n T k hk1 hk2

/--
[restrict_tiling_right_proof_irrel_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma restrict_tiling_right_proof_irrel_eq
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (k : ℕ)
  (hk1 hk2 : hasFault n T k) :
-- imply
  restrictTilingRight n T k hk1 = restrictTilingRight n T k hk2 := by
-- proof
  apply DominoTilingsZ.restrictTilingRight_proof_irrel n T k hk1 hk2

/--
[restrict_tiling_left_is_faultfree_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma restrict_tiling_left_is_faultfree_is
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (k : ℕ)
  (hk : hasFault n T k)
  (hmin : ∀ j, j < k → ¬hasFault n T j) :
-- imply
  isFaultfree k (restrictTilingLeft n T k hk) := by
-- proof
  apply DominoTilingsZ.restrictTilingLeft_isFaultfree n T k hk hmin

/--
[dominos_eq_left_part_union_right_part_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma dominos_eq_left_part_union_right_part_eq
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (k : ℕ)
  (hk : hasFault n T k) :
-- imply
  T.dominos = {d ∈ T.dominos | d.inLeftPart k} ∪ {d ∈ T.dominos | d.inRightPart k} := by
-- proof
  apply DominoTilingsZ.dominos_eq_leftPart_union_rightPart n T k hk

/--
[dominos_eq_left_union_shifted_right_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma dominos_eq_left_union_shifted_right_eq
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (k : ℕ)
  (hk : hasFault n T k) :
-- imply
  T.dominos = (restrictTilingLeft n T k hk).dominos ∪
    ((restrictTilingRight n T k hk).dominos.image (fun d => d.shiftNat k)) := by
-- proof
  apply DominoTilingsZ.dominos_eq_left_union_shifted_right n T k hk

/--
[fault_positions_finite_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma fault_positions_finite_is
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2)) :
-- imply
  (faultPositions n T).Finite := by
-- proof
  apply DominoTilingsZ.faultPositions_finite n T

/--
[min_fault_mem_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma min_fault_mem_is
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (hne : (faultPositions n T).Nonempty) :
-- imply
  minFault n T hne ∈ faultPositions n T := by
-- proof
  apply DominoTilingsZ.minFault_mem n T hne

/--
[min_fault_has_fault_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma min_fault_has_fault_is
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (hne : (faultPositions n T).Nonempty) :
-- imply
  hasFault n T (minFault n T hne) := by
-- proof
  apply DominoTilingsZ.minFault_hasFault n T hne

/--
[min_fault_le_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma min_fault_le_is
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (j : ℕ)
  (hne : (faultPositions n T).Nonempty)
  (hj : j ∈ faultPositions n T) :
-- imply
  minFault n T hne ≤ j := by
-- proof
  apply DominoTilingsZ.minFault_le n T hne j hj

/--
[fault_positions_empty_of_is_faultfree_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma fault_positions_empty_of_is_faultfree_eq
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (hff : isFaultfree n T) :
-- imply
  faultPositions n T = ∅ := by
-- proof
  apply DominoTilingsZ.faultPositions_empty_of_isFaultfree n T hff

/--
[fault_positions_not_nonempty_of_is_faultfree_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma fault_positions_not_nonempty_of_is_faultfree_is
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (hff : isFaultfree n T) :
-- imply
  ¬(faultPositions n T).Nonempty := by
-- proof
  apply DominoTilingsZ.faultPositions_not_nonempty_of_isFaultfree n T hff

/--
[partial_width_sum_one_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma partial_width_sum_one_eq
-- given
  (k : ℕ)
  (hk : k ≥ 2)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T'))) :
-- imply
  partialWidthSum k ts ⟨1, by omega⟩ = (ts ⟨0, by omega⟩).1 := by
-- proof
  apply DominoTilingsZ.partialWidthSum_one k hk ts

/--
[compose_tilings_has_fault_at_boundary_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma compose_tilings_has_fault_at_boundary_is
-- given
  (k : ℕ)
  (hk : k ≥ 2)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T'))) :
-- imply
  hasFault (composeTilings k ts).1 (composeTilings k ts).2 (ts ⟨0, by omega⟩).1 := by
-- proof
  apply DominoTilingsZ.composeTilings_hasFault_at_boundary k hk ts

/--
[compose_tilings_no_fault_before_boundary_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma compose_tilings_no_fault_before_boundary_is
-- given
  (k p : ℕ)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T')))
  (hk : k ≥ 1)
  (hp : p < (ts ⟨0, hk⟩).1) :
-- imply
  ¬hasFault (composeTilings k ts).1 (composeTilings k ts).2 p := by
-- proof
  apply DominoTilingsZ.composeTilings_no_fault_before_boundary k hk ts p hp

/--
[compose_tilings_min_fault_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma compose_tilings_min_fault_eq
-- given
  (k : ℕ)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T')))
  (hk : k ≥ 2)
  (hne : (faultPositions (composeTilings k ts).1 (composeTilings k ts).2).Nonempty) :
-- imply
  minFault (composeTilings k ts).1 (composeTilings k ts).2 hne = (ts ⟨0, by omega⟩).1 := by
-- proof
  apply DominoTilingsZ.composeTilings_minFault_eq k hk ts hne

/--
[compose_tilings_tail_width_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma compose_tilings_tail_width_eq
-- given
  (k : ℕ)
  (hk : k ≥ 2)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T'))) :
-- imply
  (composeTilings (k - 1) (faultfreeTilingsTail k (by omega) ts)).1 =
      (composeTilings k ts).1 - (ts ⟨0, by omega⟩).1 := by
-- proof
  apply DominoTilingsZ.composeTilings_tail_width k hk ts

/--
[compose_tilings_component0_in_left_part_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma compose_tilings_component0_in_left_part_is
-- given
  (k : ℕ)
  (d : Domino)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T')))
  (hk : k ≥ 1)
  (hd : d ∈ (ts ⟨0, hk⟩).2.val.dominos) :
-- imply
  d.inLeftPart (ts ⟨0, hk⟩).1 := by
-- proof
  apply DominoTilingsZ.composeTilings_component0_inLeftPart k hk ts d hd

/--
[compose_tilings_component_pos_in_right_part_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma compose_tilings_component_pos_in_right_part_is
-- given
  (k : ℕ)
  (i : Fin k)
  (d : Domino)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T')))
  (hk : k ≥ 2)
  (hi : i.val ≥ 1)
  (hd : d ∈ (ts i).2.val.dominos) :
-- imply
  (d.shiftNat (partialWidthSum k ts i)).inRightPart (ts ⟨0, by omega⟩).1 := by
-- proof
  apply DominoTilingsZ.composeTilings_componentPos_inRightPart k hk ts i hi d hd

/--
[restrict_tiling_left_compose_tilings_dominos_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma restrict_tiling_left_compose_tilings_dominos_eq
-- given
  (k : ℕ)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T')))
  (hk : k ≥ 2)
  (hfault : hasFault (composeTilings k ts).1 (composeTilings k ts).2 (ts ⟨0, by omega⟩).1) :
-- imply
  (restrictTilingLeft (composeTilings k ts).1 (composeTilings k ts).2
    (ts ⟨0, by omega⟩).1 hfault).dominos = (ts ⟨0, by omega⟩).2.val.dominos := by
-- proof
  apply DominoTilingsZ.restrictTilingLeft_composeTilings_dominos k hk ts hfault

/--
[restrict_tiling_left_compose_tilings_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma restrict_tiling_left_compose_tilings_eq
-- given
  (k : ℕ)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T')))
  (hk : k ≥ 2)
  (hfault : hasFault (composeTilings k ts).1 (composeTilings k ts).2 (ts ⟨0, by omega⟩).1) :
-- imply
  restrictTilingLeft (composeTilings k ts).1 (composeTilings k ts).2
    (ts ⟨0, by omega⟩).1 hfault = (ts ⟨0, by omega⟩).2.val := by
-- proof
  apply DominoTilingsZ.restrictTilingLeft_composeTilings_eq k hk ts hfault

/--
[compose_tilings_component_pos_dominos_unshift_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma compose_tilings_component_pos_dominos_unshift_eq
-- given
  (k : ℕ)
  (i : Fin k)
  (d : Domino)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T')))
  (hk : k ≥ 2)
  (hi : i.val ≥ 1)
  (hd : d ∈ (ts i).2.val.dominos) :
-- imply
  (d.shiftNat (partialWidthSum k ts i)).shiftNeg (ts ⟨0, by omega⟩).1 =
      d.shiftNat (partialWidthSum k ts i - (ts ⟨0, by omega⟩).1) := by
-- proof
  apply DominoTilingsZ.composeTilings_componentPos_dominos_unshift k hk ts i hi d hd

/--
[partial_width_sum_tail_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma partial_width_sum_tail_eq
-- given
  (k : ℕ)
  (hk : k ≥ 2)
  (j : Fin (k - 1))
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T'))) :
-- imply
  partialWidthSum (k - 1) (faultfreeTilingsTail k (by omega) ts) j =
    partialWidthSum k ts ⟨j.val + 1, by omega⟩ - (ts ⟨0, by omega⟩).1 := by
-- proof
  apply DominoTilingsZ.partialWidthSum_tail k hk ts j

/--
[restrict_tiling_right_compose_tilings_dominos_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma restrict_tiling_right_compose_tilings_dominos_eq
-- given
  (k : ℕ)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T')))
  (hk : k ≥ 2)
  (hfault : hasFault (composeTilings k ts).1 (composeTilings k ts).2 (ts ⟨0, by omega⟩).1) :
-- imply
  (restrictTilingRight (composeTilings k ts).1 (composeTilings k ts).2
        (ts ⟨0, by omega⟩).1 hfault).dominos =
      (composeTilings (k - 1) (faultfreeTilingsTail k (by omega) ts)).2.dominos := by
-- proof
  apply DominoTilingsZ.restrictTilingRight_composeTilings_dominos k hk ts hfault

/--
[restrict_tiling_right_compose_tilings_dominos_eq_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma restrict_tiling_right_compose_tilings_dominos_eq_eq
-- given
  (k : ℕ)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T')))
  (hk : k ≥ 2)
  (hfault : hasFault (composeTilings k ts).1 (composeTilings k ts).2 (ts ⟨0, by omega⟩).1) :
-- imply
  (restrictTilingRight (composeTilings k ts).1 (composeTilings k ts).2
        (ts ⟨0, by omega⟩).1 hfault).dominos =
      (composeTilings (k - 1) (faultfreeTilingsTail k (by omega) ts)).2.dominos := by
-- proof
  apply DominoTilingsZ.restrictTilingRight_composeTilings_dominos_eq k hk ts hfault

/--
[restrict_tiling_right_compose_tilings_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma restrict_tiling_right_compose_tilings_eq
-- given
  (k : ℕ)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T')))
  (hk : k ≥ 2)
  (hfault : hasFault (composeTilings k ts).1 (composeTilings k ts).2 (ts ⟨0, by omega⟩).1) :
-- imply
  restrictTilingRight (composeTilings k ts).1 (composeTilings k ts).2
    (ts ⟨0, by omega⟩).1 hfault =
    (composeTilings_tail_width k hk ts) ▸ (composeTilings (k - 1) (faultfreeTilingsTail k (by omega) ts)).2 := by
-- proof
  apply DominoTilingsZ.restrictTilingRight_composeTilings_eq k hk ts hfault

/--
[decompose_tiling_has_fault_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma decompose_tiling_has_fault_eq
-- given
  (n : ℕ)
  (T : Tiling (Rectangle (n + 1) 2))
  (hne : (faultPositions (n + 1) T).Nonempty) :
-- imply
  let k := minFault (n + 1) T hne
  let hk := minFault_hasFault (n + 1) T hne
  let hk_min : ∀ j, j < k → ¬hasFault (n + 1) T j := fun j hj hfault =>
    absurd (minFault_le (n + 1) T hne j hfault) (not_le.mpr hj)
  let left := restrictTilingLeft (n + 1) T k hk
  let left_ff := restrictTilingLeft_isFaultfree (n + 1) T k hk hk_min
  let right := restrictTilingRight (n + 1) T k hk
  let ⟨m, ts⟩ := decomposeTiling (n + 1 - k) right
  decomposeTiling (n + 1) T =
    ⟨m + 1, fun i => if hi : i.val = 0 then ⟨k, ⟨left, left_ff⟩⟩
                     else ts ⟨i.val - 1, by omega⟩⟩ := by
-- proof
  apply DominoTilingsZ.decomposeTiling_hasFault n T hne

/--
[decompose_tiling_has_fault_fst_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma decompose_tiling_has_fault_fst_eq
-- given
  (n : ℕ)
  (T : Tiling (Rectangle (n + 1) 2))
  (hne : (faultPositions (n + 1) T).Nonempty) :
-- imply
  let k := minFault (n + 1) T hne
  let hk := minFault_hasFault (n + 1) T hne
  let right := restrictTilingRight (n + 1) T k hk
  (decomposeTiling (n + 1) T).1 = (decomposeTiling (n + 1 - k) right).1 + 1 := by
-- proof
  apply DominoTilingsZ.decomposeTiling_hasFault_fst n T hne

/--
[compose_tilings_decompose_tiling_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma compose_tilings_decompose_tiling_eq
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2)) :
-- imply
  let ⟨k, ts⟩ := decomposeTiling n T
  composeTilings k ts = ⟨n, T⟩ := by
-- proof
  apply DominoTilingsZ.composeTilings_decomposeTiling n T

/--
[decompose_tiling_faultfree_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma decompose_tiling_faultfree_eq
-- given
  (n : ℕ)
  (T : Tiling (Rectangle (n + 1) 2))
  (hff : isFaultfree (n + 1) T) :
-- imply
  decomposeTiling (n + 1) T = ⟨1, fun _ => ⟨n + 1, ⟨T, hff⟩⟩⟩ := by
-- proof
  apply DominoTilingsZ.decomposeTiling_faultfree n T hff

/--
[decompose_tiling_subst_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma decompose_tiling_subst_eq
-- given
  {n m : ℕ}
  (h : n = m)
  (T : Tiling (Rectangle n 2)) :
-- imply
  decomposeTiling n T = decomposeTiling m (h ▸ T) := by
-- proof
  apply DominoTilingsZ.decomposeTiling_subst h T

/--
[decompose_tiling_eq_of_dominos_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma decompose_tiling_eq_of_dominos_eq
-- given
  {n m : ℕ}
  (T1 : Tiling (Rectangle n 2))
  (T2 : Tiling (Rectangle m 2))
  (h : n = m)
  (hdom : T1.dominos = T2.dominos) :
-- imply
  decomposeTiling n T1 = decomposeTiling m T2 := by
-- proof
  apply DominoTilingsZ.decomposeTiling_eq_of_dominos_eq h T1 T2 hdom

/--
[restrict_tiling_left_subst_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma restrict_tiling_left_subst_eq
-- given
  {n m : ℕ}
  (T : Tiling (Rectangle n 2))
  (k : ℕ)
  (h : n = m)
  (hk : hasFault n T k) :
-- imply
  restrictTilingLeft m (h ▸ T) k (by subst h; exact hk) =
      restrictTilingLeft n T k hk := by
-- proof
  apply DominoTilingsZ.restrictTilingLeft_subst h T k hk

/--
[restrict_tiling_right_subst_dominos_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma restrict_tiling_right_subst_dominos_eq
-- given
  {n m : ℕ}
  (T : Tiling (Rectangle n 2))
  (k : ℕ)
  (h : n = m)
  (hk : hasFault n T k) :
-- imply
  (restrictTilingRight m (h ▸ T) k (by subst h; exact hk)).dominos =
      (restrictTilingRight n T k hk).dominos := by
-- proof
  apply DominoTilingsZ.restrictTilingRight_subst_dominos h T k hk

/--
[decompose_tiling_compose_tilings_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma decompose_tiling_compose_tilings_eq
-- given
  (k : ℕ)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T'))) :
-- imply
  decomposeTiling (composeTilings k ts).1 (composeTilings k ts).2 = ⟨k, ts⟩ := by
-- proof
  apply DominoTilingsZ.decomposeTiling_composeTilings k ts

/--
[compose_tilings_width_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma compose_tilings_width_eq
-- given
  (k : ℕ)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T'))) :
-- imply
  (composeTilings k ts).1 = ∑ i : Fin k, (ts i).1 := by
-- proof
  apply DominoTilingsZ.composeTilings_width k ts

/--
[decompose_tiling_weight_sum_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma decompose_tiling_weight_sum_eq
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2)) :
-- imply
  let ⟨k, ts⟩ := decomposeTiling n T
  (∑ i : Fin k, (ts i).1) = n := by
-- proof
  apply DominoTilingsZ.decomposeTiling_weight_sum n T

/--
[tiling_decomposition_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma tiling_decomposition_eq
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2)) :
-- imply
  ∃ (k : ℕ) (ts : Fin k → Σ m, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T')),
        (∑ i, (ts i).1) = n := by
-- proof
  apply DominoTilingsZ.tiling_decomposition n T

/--
[vertical_11_not_in_shift_nat_image_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma vertical_11_not_in_shift_nat_image_is
-- given
  (m : ℕ)
  (T : Tiling (Rectangle m 2)) :
-- imply
  Domino.vertical 1 1 ∉ T.dominos.image (fun d => d.shiftNat 1) := by
-- proof
  apply DominoTilingsZ.vertical_11_not_in_shiftNat_image m T

/--
[horizontal_11_not_in_shift_nat2_image_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma horizontal_11_not_in_shift_nat2_image_is
-- given
  (m : ℕ)
  (T : Tiling (Rectangle m 2)) :
-- imply
  Domino.horizontal 1 1 ∉ T.dominos.image (fun d => d.shiftNat 2) := by
-- proof
  apply DominoTilingsZ.horizontal_11_not_in_shiftNat2_image m T

/--
[horizontal_12_not_in_shift_nat2_image_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma horizontal_12_not_in_shift_nat2_image_is
-- given
  (m : ℕ)
  (T : Tiling (Rectangle m 2)) :
-- imply
  Domino.horizontal 1 2 ∉ T.dominos.image (fun d => d.shiftNat 2) := by
-- proof
  apply DominoTilingsZ.horizontal_12_not_in_shiftNat2_image m T

/--
[vertical_11_not_in_shift_nat2_image_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma vertical_11_not_in_shift_nat2_image_is
-- given
  (m : ℕ)
  (T : Tiling (Rectangle m 2)) :
-- imply
  Domino.vertical 1 1 ∉ T.dominos.image (fun d => d.shiftNat 2) := by
-- proof
  apply DominoTilingsZ.vertical_11_not_in_shiftNat2_image m T

/--
[num_tilings_recurrence_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma num_tilings_recurrence_eq
-- given
  (n : ℕ) :
-- imply
  numTilings (n + 2) 2 = numTilings n 2 + numTilings (n + 1) 2 := by
-- proof
  apply DominoTilingsZ.numTilings_recurrence n

/--
[num_tilings_2_n_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma num_tilings_2_n_eq
-- given
  (n : ℕ) :
-- imply
  numTilings n 2 = Nat.fib (n + 1) := by
-- proof
  apply DominoTilingsZ.numTilings_2_n n

/--
[count_of_weight_tilings_height2_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma count_of_weight_tilings_height2_eq
-- given
  (n : ℕ) :
-- imply
  TilingsHeight2.countOfWeight tilingsHeight2_isFiniteType n = numTilings n 2 := by
-- proof
  apply DominoTilingsZ.countOfWeight_tilingsHeight2_eq n

/--
[weight_gen_fun_tilings_height2_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma weight_gen_fun_tilings_height2_eq :
-- imply
  TilingsHeight2.weightGenFun (R := ℚ) tilingsHeight2_isFiniteType =
    PowerSeries.mk fun n => (Nat.fib (n + 1) : ℚ) := by
-- proof
  apply DominoTilingsZ.weightGenFun_tilingsHeight2

/--
[dominos_in_rectangle_finite_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma dominos_in_rectangle_finite_is
-- given
  (n m : ℕ) :
-- imply
  Set.Finite (DominosInRectangle n m) := by
-- proof
  apply DominoTilingsZ.dominosInRectangle_finite n m

/--
[tiling_dominos_subset_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma tiling_dominos_subset_is
-- given
  (n m : ℕ)
  (T : Tiling (Rectangle n m)) :
-- imply
  T.dominos ⊆ DominosInRectangle n m := by
-- proof
  apply DominoTilingsZ.tiling_dominos_subset n m T

/--
[tilings_finite_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma tilings_finite_is
-- given
  (n m : ℕ) :
-- imply
  Set.Finite (Set.univ : Set (Tiling (Rectangle n m))) := by
-- proof
  apply DominoTilingsZ.tilings_finite n m


-- created on 2026-10-20
