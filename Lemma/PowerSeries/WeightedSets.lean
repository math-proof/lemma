import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet WeightedSetExamples DominoTilingsZ


section
-- ac-theorems


open PowerSeries Finset BigOperators

noncomputable section

variable {R : Type*} [CommSemiring R]

namespace WeightedSet

variable {α β γ : Type*}

/-- Alternative characterization: weightGenFun = ∑_{a ∈ A} x^{|a|} -/
lemma weightGenFun_eq_sum (W : WeightedSet α) (hft : W.IsFiniteType) :
    W.weightGenFun (R := R) hft = PowerSeries.mk fun n => ((hft n).toFinset.card : R) := by
  rfl

/-- Isomorphic finite-type weighted sets have equal weight generating functions.
    (Proposition \ref{prop.gf-ws.iso}) -/
lemma weightGenFun_eq_of_isomorphic (W₁ : WeightedSet α) (W₂ : WeightedSet β)
    (hft₁ : W₁.IsFiniteType) (hft₂ : W₂.IsFiniteType) (h : W₁ ≅ᵥ W₂) :
    W₁.weightGenFun (R := R) hft₁ = W₂.weightGenFun hft₂ := by
  obtain ⟨iso⟩ := h
  ext n
  simp only [weightGenFun, coeff_mk, countOfWeight]
  congr 1
  rw [← Nat.card_eq_card_finite_toFinset (hft₁ n), ← Nat.card_eq_card_finite_toFinset (hft₂ n)]
  apply Nat.card_congr
  refine Equiv.subtypeEquiv iso.toEquiv ?_
  intro a
  simp only [Set.mem_ofPred_eq]
  rw [iso.weight_eq]

@[simp] lemma disjointUnion_weight_inl (W₁ : WeightedSet α) (W₂ : WeightedSet β) (a : α) :
    (W₁ +ᵥ W₂).weight (Sum.inl a) = W₁.weight a := rfl

@[simp] lemma disjointUnion_weight_inr (W₁ : WeightedSet α) (W₂ : WeightedSet β) (b : β) :
    (W₁ +ᵥ W₂).weight (Sum.inr b) = W₂.weight b := rfl

/-- The disjoint union of finite-type weighted sets is finite-type. -/
lemma disjointUnion_isFiniteType (W₁ : WeightedSet α) (W₂ : WeightedSet β)
    (hft₁ : W₁.IsFiniteType) (hft₂ : W₂.IsFiniteType) : (W₁ +ᵥ W₂).IsFiniteType := by
  intro n
  -- The set of elements of weight n in the disjoint union is the disjoint union
  -- of the sets of elements of weight n in each component
  have h1 : {a : α ⊕ β | (W₁ +ᵥ W₂).weight a = n} =
      Sum.inl '' {a : α | W₁.weight a = n} ∪ Sum.inr '' {b : β | W₂.weight b = n} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_image]
    constructor
    · intro hx
      cases x with
      | inl a =>
        left
        exact ⟨a, hx, rfl⟩
      | inr b =>
        right
        exact ⟨b, hx, rfl⟩
    · intro hx
      rcases hx with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
      · exact ha
      · exact hb
  rw [h1]
  exact Set.Finite.union (Set.Finite.image _ (hft₁ n)) (Set.Finite.image _ (hft₂ n))

/-- The weight generating function of a disjoint union is the sum of the generating functions.
    (Proposition \ref{prop.gf-ws.djun}) -/
lemma weightGenFun_disjointUnion (W₁ : WeightedSet α) (W₂ : WeightedSet β)
    (hft₁ : W₁.IsFiniteType) (hft₂ : W₂.IsFiniteType) :
    (W₁ +ᵥ W₂).weightGenFun (R := R) (disjointUnion_isFiniteType W₁ W₂ hft₁ hft₂) =
      W₁.weightGenFun hft₁ + W₂.weightGenFun hft₂ := by
  ext n
  simp only [weightGenFun, PowerSeries.coeff_mk, map_add, countOfWeight]
  -- Use ncard which is independent of the proof of finiteness
  have h1 := hft₁ n
  have h2 := hft₂ n
  have hft_union := disjointUnion_isFiniteType W₁ W₂ hft₁ hft₂ n
  -- Convert to ncard
  have eq1 : (h1.toFinset.card : R) = ({a : α | W₁.weight a = n}.ncard : R) := by
    rw [Set.ncard_eq_toFinset_card _ h1]
  have eq2 : (h2.toFinset.card : R) = ({b : β | W₂.weight b = n}.ncard : R) := by
    rw [Set.ncard_eq_toFinset_card _ h2]
  have eq_union : (hft_union.toFinset.card : R) = ({x : α ⊕ β | (W₁ +ᵥ W₂).weight x = n}.ncard : R) := by
    rw [Set.ncard_eq_toFinset_card _ hft_union]
  rw [eq1, eq2, eq_union]
  -- Establish the set equality: elements of weight n in the disjoint union are
  -- either from W₁ or W₂
  have hset : {x : α ⊕ β | (W₁ +ᵥ W₂).weight x = n} =
              (Sum.inl (β := β)) '' {a : α | W₁.weight a = n} ∪ (Sum.inr (α := α)) '' {b : β | W₂.weight b = n} := by
    ext x
    simp only [disjointUnion, Set.mem_ofPred_eq, Set.mem_union, Set.mem_image]
    constructor
    · intro hx
      cases x with
      | inl a => left; exact ⟨a, hx, rfl⟩
      | inr b => right; exact ⟨b, hx, rfl⟩
    · intro hx
      rcases hx with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
      · exact ha
      · exact hb
  -- The two images are disjoint (Sum.inl and Sum.inr have disjoint ranges)
  have hdisj : Disjoint ((Sum.inl (β := β)) '' {a : α | W₁.weight a = n})
                        ((Sum.inr (α := α)) '' {b : β | W₂.weight b = n}) := by
    rw [Set.disjoint_iff]
    intro x ⟨⟨a, _, ha⟩, ⟨b, _, hb⟩⟩
    cases ha
    simp at hb
  have h1' : ((Sum.inl (β := β)) '' {a : α | W₁.weight a = n}).Finite := h1.image Sum.inl
  have h2' : ((Sum.inr (α := α)) '' {b : β | W₂.weight b = n}).Finite := h2.image Sum.inr
  -- The ncard of a disjoint union is the sum of ncards
  have ncard_eq : {x : α ⊕ β | (W₁ +ᵥ W₂).weight x = n}.ncard =
                  {a : α | W₁.weight a = n}.ncard + {b : β | W₂.weight b = n}.ncard := by
    rw [hset, Set.ncard_union_eq hdisj h1' h2']
    rw [Set.ncard_image_of_injective _ Sum.inl_injective]
    rw [Set.ncard_image_of_injective _ Sum.inr_injective]
  simp only [ncard_eq, Nat.cast_add]

@[simp] lemma prod_weight (W₁ : WeightedSet α) (W₂ : WeightedSet β) (p : α × β) :
    (W₁ ×ᵥ W₂).weight p = W₁.weight p.1 + W₂.weight p.2 := rfl

/-- The product of finite-type weighted sets is finite-type.
    (Proof of first part of Proposition \ref{prop.gf-ws.prod}) -/
lemma prod_isFiniteType (W₁ : WeightedSet α) (W₂ : WeightedSet β)
    (hft₁ : W₁.IsFiniteType) (hft₂ : W₂.IsFiniteType) : (W₁ ×ᵥ W₂).IsFiniteType := by
  intro n
  -- The set of pairs with weight n is a subset of ⋃_{i ≤ n} {a | weight a = i} × {b | weight b = n - i}
  have h : {p : α × β | (W₁ ×ᵥ W₂).weight p = n} ⊆
      ⋃ i ∈ Finset.range (n + 1), {a | W₁.weight a = i} ×ˢ {b | W₂.weight b = n - i} := by
    intro ⟨a, b⟩ hab
    simp only [prod, Set.mem_ofPred_eq] at hab
    simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_ofPred_eq, Finset.mem_range]
    refine ⟨W₁.weight a, ?_, rfl, ?_⟩
    · omega
    · omega
  apply Set.Finite.subset _ h
  apply Set.Finite.biUnion
  · exact (Finset.range (n + 1)).finite_toSet
  · intro i _
    exact Set.Finite.prod (hft₁ i) (hft₂ (n - i))

/-- The weight generating function of a product is the product of the generating functions.
    (Proposition \ref{prop.gf-ws.prod})

    This is the key theorem showing that the weight generating function respects
    Cartesian products: ḡ(A × B) = ḡ(A) · ḡ(B). The proof partitions the pairs of
    total weight n by the weight of the first component, showing this equals the
    convolution sum that defines multiplication of power series. -/
lemma weightGenFun_prod [DecidableEq α] [DecidableEq β] (W₁ : WeightedSet α) (W₂ : WeightedSet β)
    (hft₁ : W₁.IsFiniteType) (hft₂ : W₂.IsFiniteType) :
    (W₁ ×ᵥ W₂).weightGenFun (R := R) (prod_isFiniteType W₁ W₂ hft₁ hft₂) =
      W₁.weightGenFun hft₁ * W₂.weightGenFun hft₂ := by
  classical
  ext n
  rw [PowerSeries.coeff_mul]
  simp only [weightGenFun, PowerSeries.coeff_mk, countOfWeight]
  -- The count of weight n in product equals sum over (i,j) with i+j=n of products of counts
  have hft_prod := prod_isFiniteType W₁ W₂ hft₁ hft₂
  -- Show that the toFinset of the product weight set equals the biUnion of toFinsets
  have key : (hft_prod n).toFinset =
      (antidiagonal n).biUnion (fun ij => (hft₁ ij.1).toFinset ×ˢ (hft₂ ij.2).toFinset) := by
    ext ⟨a, b⟩
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, mem_biUnion, mem_product, prod]
    constructor
    · intro h
      refine ⟨(W₁.weight a, W₂.weight b), ?_, rfl, rfl⟩
      exact (HasAntidiagonal.mem_antidiagonal).mpr h
    · rintro ⟨⟨i, j⟩, hij, ha, hb⟩
      rw [ha, hb]
      exact (HasAntidiagonal.mem_antidiagonal).mp hij
  rw [key]
  -- The biUnion is disjoint, so card equals sum of cards
  have hdisj : (antidiagonal n : Set (ℕ × ℕ)).PairwiseDisjoint
      (fun ij => (hft₁ ij.1).toFinset ×ˢ (hft₂ ij.2).toFinset) := by
    intro ⟨i₁, j₁⟩ _ ⟨i₂, j₂⟩ _ hne
    simp only [Function.onFun, Finset.disjoint_iff_ne]
    intro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
    simp only [mem_product, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hab hab'
    apply hne
    simp only [Prod.mk.injEq] at heq
    obtain ⟨ha_eq, hb_eq⟩ := heq
    rw [← hab.1, ← hab.2, ha_eq, hb_eq, hab'.1, hab'.2]
  rw [card_biUnion hdisj]
  simp only [card_product]
  -- Convert ↑(∑ ...) to ∑ ↑(...)
  push_cast
  rfl

/-- The k-th power of a finite-type weighted set is finite-type. -/
lemma pow_isFiniteType (W : WeightedSet α) (hft : W.IsFiniteType) (k : ℕ) :
    (W.pow k).IsFiniteType := by
  intro n
  -- Show {a | W.weight a ≤ n} is finite (finite union of finite sets)
  have h_le_finite : Set.Finite {a : α | W.weight a ≤ n} := by
    have : {a : α | W.weight a ≤ n} = ⋃ m ≤ n, {a | W.weight a = m} := by
      ext a; simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
      exact ⟨fun h => ⟨W.weight a, h, rfl⟩, fun ⟨_, hm, ha⟩ => ha ▸ hm⟩
    rw [this]
    exact Set.Finite.biUnion (Set.finite_le_nat n) fun m _ => hft m
  -- The set of f with weight n is a subset of f where each component has weight ≤ n
  apply Set.Finite.subset (Set.Finite.pi' fun _ => h_le_finite)
  intro f hf i
  simp only [Set.mem_ofPred_eq, pow] at hf ⊢
  exact (Finset.single_le_sum (by simp) (Finset.mem_univ i)).trans_eq hf

/-- The weight generating function of A^k is (ḡ(A))^k.
    (Proposition \ref{prop.gf-ws.pow}) -/
lemma weightGenFun_pow (W : WeightedSet α) (hft : W.IsFiniteType) (k : ℕ) :
    (W.pow k).weightGenFun (R := R) (pow_isFiniteType W hft k) =
      (W.weightGenFun hft) ^ k := by
  classical
  induction k with
  | zero =>
    simp only [pow_zero]
    ext n
    simp only [weightGenFun, countOfWeight, PowerSeries.coeff_mk, PowerSeries.coeff_one]
    split_ifs with hn
    · -- n = 0: Show that there's exactly one element of weight 0
      subst hn
      have heq : {f : Fin 0 → α | ∑ i : Fin 0, W.weight (f i) = 0} = Set.univ := by
        ext f
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        rfl
      have hFinset : (pow_isFiniteType W hft 0 0).toFinset = Finset.univ := by
        ext f
        simp only [Set.Finite.mem_toFinset, pow, heq, Set.mem_univ, Finset.mem_univ]
      rw [hFinset]
      have : Unique (Fin 0 → α) := Pi.uniqueOfIsEmpty fun _ => α
      simp
    · -- n ≠ 0: No function Fin 0 → α has weight n > 0
      have heq : {f : Fin 0 → α | ∑ i : Fin 0, W.weight (f i) = n} = ∅ := by
        ext f
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        have : ∑ i : Fin 0, W.weight (f i) = 0 := rfl
        omega
      have hFinset : (pow_isFiniteType W hft 0 n).toFinset = ∅ := by
        ext f
        rw [Set.Finite.mem_toFinset]
        simp only [pow, heq, Set.mem_empty_iff_false]
        simp
      rw [hFinset]
      simp
  | succ n ih =>
    have hiso : (W.pow (n + 1)) ≅ᵥ (W ×ᵥ (W.pow n)) := ⟨pow_succ_equiv W n⟩
    calc (W.pow (n + 1)).weightGenFun (R := R) (pow_isFiniteType W hft (n + 1))
        = (W ×ᵥ (W.pow n)).weightGenFun (prod_isFiniteType W (W.pow n) hft (pow_isFiniteType W hft n)) := by
          exact weightGenFun_eq_of_isomorphic _ _ _ _ hiso
      _ = W.weightGenFun hft * (W.pow n).weightGenFun (pow_isFiniteType W hft n) := by
          exact weightGenFun_prod _ _ _ _
      _ = W.weightGenFun hft * (W.weightGenFun hft) ^ n := by rw [ih]
      _ = (W.weightGenFun hft) ^ (n + 1) := by ring

/-- The weight in the tuples weighted set equals the weight in the corresponding power -/
lemma tuples_weight_eq_pow (W : WeightedSet α) (n : ℕ) (f : Fin n → α) :
    W.tuples.weight ⟨n, f⟩ = (W.pow n).weight f := by
  simp only [tuples, pow]

/-- The tuples weighted set is finite-type if the original is finite-type and has positive weights.
    
    Note: The hypothesis `hpos : W.HasPositiveWeights` is necessary. Without it, the theorem is false:
    if W has elements of weight 0, then for any weight m, there are infinitely many tuples of weight m
    (we can have arbitrarily many weight-0 elements in a tuple). For example, if W = ℕ with weight = id,
    then tuples of weight 2 include ⟨1, ![2]⟩, ⟨2, ![0, 2]⟩, ⟨3, ![0, 0, 2]⟩, etc.
    
    The key insight is that with positive weights, a tuple of length n has weight ≥ n, so for weight m,
    we only need to consider tuples of length ≤ m. -/
lemma tuples_isFiniteType (W : WeightedSet α) (hft : W.IsFiniteType)
    (hpos : W.HasPositiveWeights) : W.tuples.IsFiniteType := by
  intro m
  -- Key: if every element has weight ≥ 1, then a tuple of length n has weight ≥ n
  -- So for weight = m, we can only have tuples of length ≤ m
  have h : {p : Σ n : ℕ, Fin n → α | W.tuples.weight p = m} ⊆
      ⋃ n ∈ Finset.range (m + 1), Sigma.mk n '' {f : Fin n → α | (W.pow n).weight f = m} := by
    intro ⟨n, f⟩ hf
    simp only [tuples, Set.mem_ofPred_eq] at hf
    simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_range, pow, Set.mem_ofPred_eq]
    refine ⟨n, ?_, f, hf, rfl⟩
    -- Need to show n < m + 1, i.e., n ≤ m
    -- Since each element has weight ≥ 1, sum of n weights ≥ n
    have hge : ∑ i : Fin n, W.weight (f i) ≥ n := by
      calc ∑ i : Fin n, W.weight (f i) ≥ ∑ i : Fin n, 1 := 
        Finset.sum_le_sum (fun i _ => hpos (f i))
        _ = n := by simp
    omega
  apply Set.Finite.subset _ h
  apply Set.Finite.biUnion
  · exact (Finset.range (m + 1)).finite_toSet
  · intro n _
    -- {f : Fin n → α | (W.pow n).weight f = m} is finite by pow_isFiniteType
    exact Set.Finite.image _ (pow_isFiniteType W hft n m)

end WeightedSet


namespace WeightedSetExamples

/-- The binary strings weighted set is finite-type -/
lemma binaryStrings_isFiniteType : BinaryStrings.IsFiniteType := fun n =>
  Set.finite_coe_iff.mp (Finite.of_fintype (List.Vector (Fin 2) n))

/-- Helper lemma: the count of binary strings of length n is 2^n -/
lemma binaryStrings_countOfWeight (n : ℕ) :
    BinaryStrings.countOfWeight binaryStrings_isFiniteType n = 2 ^ n := by
  unfold WeightedSet.countOfWeight
  have h_eq : {a : List (Fin 2) | BinaryStrings.weight a = n} =
              Set.range (List.Vector.toList : List.Vector (Fin 2) n → List (Fin 2)) := by
    ext l
    simp only [Set.mem_ofPred_eq, Set.mem_range, BinaryStrings]
    constructor
    · intro hl; exact ⟨⟨l, hl⟩, rfl⟩
    · intro ⟨v, hv⟩; rw [← hv]; exact v.toList_length
  have h_inj : Function.Injective (List.Vector.toList : List.Vector (Fin 2) n → List (Fin 2)) := by
    intro v w h
    exact List.Vector.toList_injective h
  have h_finite := binaryStrings_isFiniteType n
  have h_card : h_finite.toFinset.card = {a : List (Fin 2) | BinaryStrings.weight a = n}.ncard := by
    rw [Set.ncard]
    simp only [h_finite.encard_eq_coe_toFinset_card, ENat.toNat_natCast]
  rw [h_card, h_eq]
  rw [Set.ncard_range_of_injective h_inj]
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.ofEquiv_card (Equiv.vectorEquivFin (Fin 2) n).symm]
  simp [Fintype.card_fin]

/-- The generating function of binary strings is 1/(1-2x).
    Since (mk 1) represents 1 + x + x² + ... = 1/(1-x),
    we express 1/(1-2x) differently. -/
lemma weightGenFun_binaryStrings :
    BinaryStrings.weightGenFun (R := ℚ) binaryStrings_isFiniteType =
      PowerSeries.mk fun n => (2 ^ n : ℚ) := by
  ext n
  simp only [WeightedSet.weightGenFun, PowerSeries.coeff_mk]
  rw [binaryStrings_countOfWeight]
  simp

/-- Positive integers form a finite-type weighted set -/
lemma positiveIntegers_isFiniteType : PositiveIntegers.IsFiniteType := by
  intro n
  -- The set {a : ℕ+ | a.val = n} has at most one element
  apply Set.Subsingleton.finite
  intro x hx y hy
  simp only [Set.mem_ofPred_eq, PositiveIntegers] at hx hy
  exact PNat.eq (hx.trans hy.symm)

lemma countOfWeight_zero : PositiveIntegers.countOfWeight positiveIntegers_isFiniteType 0 = 0 := by
  simp only [WeightedSet.countOfWeight]
  convert Finset.card_empty
  simp only [Set.Finite.toFinset_eq_empty]
  ext x
  simp only [PositiveIntegers, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  exact x.2.ne'

lemma countOfWeight_pos (n : ℕ) (hn : 0 < n) :
    PositiveIntegers.countOfWeight positiveIntegers_isFiniteType n = 1 := by
  unfold WeightedSet.countOfWeight
  let a : ℕ+ := ⟨n, hn⟩
  have hset : {x : ℕ+ | PositiveIntegers.weight x = n} = {a} := by
    ext x
    simp only [PositiveIntegers, Set.mem_ofPred_eq, a]
    exact ⟨fun hx => Subtype.ext hx, fun hx => hx ▸ rfl⟩
  have hfin : ({a} : Set ℕ+).Finite := Set.finite_singleton a
  have heq : (positiveIntegers_isFiniteType n).toFinset = hfin.toFinset :=
    Set.Finite.toFinset_inj.mpr hset
  rw [heq, Set.Finite.toFinset_singleton, Finset.card_singleton]

/-- The generating function of positive integers is x + x² + x³ + ... = x/(1-x) -/
lemma weightGenFun_positiveIntegers :
    PositiveIntegers.weightGenFun (R := ℚ) positiveIntegers_isFiniteType =
      PowerSeries.X * (PowerSeries.invOneSubPow ℚ 1).val := by
  ext n
  simp only [WeightedSet.weightGenFun, coeff_mk]
  cases n with
  | zero =>
    simp [countOfWeight_zero, coeff_zero_X_mul]
  | succ n =>
    rw [coeff_succ_X_mul]
    rw [countOfWeight_pos (n + 1) (Nat.succ_pos n)]
    rw [show (1 : ℕ) = 0 + 1 from rfl, invOneSubPow_val_succ_eq_mk_add_choose]
    simp

/-- Compositions form a finite-type weighted set -/
lemma compositions_isFiniteType (k : ℕ) : (Compositions k).IsFiniteType :=
  WeightedSet.pow_isFiniteType _ positiveIntegers_isFiniteType k

/-- The generating function of compositions of length k is (x/(1-x))^k -/
lemma weightGenFun_compositions (k : ℕ) :
    (Compositions k).weightGenFun (R := ℚ) (compositions_isFiniteType k) =
      (PowerSeries.X * (PowerSeries.invOneSubPow ℚ 1).val) ^ k := by
  -- Compositions k = PositiveIntegers.pow k by definition
  -- By weightGenFun_pow, the generating function of A^k is (ḡ(A))^k
  -- By weightGenFun_positiveIntegers, ḡ(PositiveIntegers) = X * (invOneSubPow ℚ 1).val
  simp only [Compositions]
  rw [WeightedSet.weightGenFun_pow PositiveIntegers positiveIntegers_isFiniteType k,
      weightGenFun_positiveIntegers]

end WeightedSetExamples


namespace DominoTilingsZ


/-- Membership in a rectangle -/
lemma mem_rectangle_iff {n m : ℕ} {p : ℤ × ℤ} :
    p ∈ Rectangle n m ↔ 1 ≤ p.1 ∧ p.1 ≤ n ∧ 1 ≤ p.2 ∧ p.2 ≤ m := Iff.rfl

lemma cell_11_in_rect (n : ℕ) (hn : n ≥ 1) : (1, 1) ∈ Rectangle n 2 := by
  simp only [Rectangle, Set.mem_ofPred_eq]; omega

lemma exists_domino_covering_11 (n : ℕ) (hn : n ≥ 1) (T : Tiling (Rectangle n 2)) :
    ∃ d ∈ T.dominos, (1, 1) ∈ d.toShape := by
  have h11 : (1, 1) ∈ Rectangle n 2 := cell_11_in_rect n hn
  rw [← T.cover] at h11
  simp only [Set.mem_iUnion] at h11
  obtain ⟨d, hd, hmem⟩ := h11
  exact ⟨d, hd, hmem⟩
/-- The n × 0 rectangle is empty -/
@[simp]
lemma Rectangle_zero_right (n : ℕ) : Rectangle n 0 = ∅ := by
  ext p
  simp only [Rectangle, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro h1 _ h3
  omega

/-- The rectangle has n * m cells -/
lemma Rectangle_ncard (n m : ℕ) : (Rectangle n m).ncard = n * m := by
  have h : Rectangle n m = Set.Icc (1 : ℤ) n ×ˢ Set.Icc (1 : ℤ) m := by
    ext ⟨x, y⟩
    simp only [Rectangle, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_Icc]
    tauto
  rw [h, Set.ncard_prod]
  simp [Set.ncard_eq_toFinset_card', Set.toFinset_Icc]

/-- A domino covers exactly 2 cells -/
lemma Domino.toShape_ncard (d : Domino) : d.toShape.ncard = 2 := by
  cases d with
  | horizontal i j =>
    simp only [toShape]
    rw [Set.ncard_pair]
    simp only [Prod.mk.injEq, ne_eq, not_and]
    intro _
    omega
  | vertical i j =>
    simp only [toShape]
    rw [Set.ncard_pair]
    simp only [Prod.mk.injEq, ne_eq, not_and]
    intro _ _
    omega

/-- A horizontal domino covers the cells (i,j) and (i+1,j) -/
@[simp]
lemma Domino.horizontal_toShape (i j : ℤ) :
    (Domino.horizontal i j).toShape = {(i, j), (i + 1, j)} := rfl

/-- A vertical domino covers the cells (i,j) and (i,j+1) -/
@[simp]
lemma Domino.vertical_toShape (i j : ℤ) :
    (Domino.vertical i j).toShape = {(i, j), (i, j + 1)} := rfl

/-- The shape of a domino is finite -/
lemma Domino.toShape_finite (d : Domino) : d.toShape.Finite := by
  cases d <;> simp only [toShape, Set.finite_insert, Set.finite_singleton]

/-- Two dominos with the same shape are equal.
    This follows from the fact that a domino's shape uniquely determines its type and position. -/
lemma Domino.eq_of_toShape_eq {d1 d2 : Domino} (h : d1.toShape = d2.toShape) : d1 = d2 := by
  cases d1 with
  | horizontal i1 j1 =>
    cases d2 with
    | horizontal i2 j2 =>
      simp only [toShape] at h
      have h1 : (i1, j1) ∈ ({(i2, j2), (i2 + 1, j2)} : Set (ℤ × ℤ)) := by rw [← h]; exact Set.mem_insert _ _
      have h2 : (i1 + 1, j1) ∈ ({(i2, j2), (i2 + 1, j2)} : Set (ℤ × ℤ)) := by rw [← h]; exact Set.mem_insert_of_mem _ rfl
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h1 h2
      rcases h1 with ⟨hi1, hj1⟩ | ⟨hi1, hj1⟩
      · rcases h2 with ⟨hi2, hj2⟩ | ⟨hi2, hj2⟩ <;> [omega; simp only [hi1, hj1]]
      · rcases h2 with ⟨hi2, hj2⟩ | ⟨hi2, hj2⟩ <;> omega
    | vertical i2 j2 =>
      simp only [toShape] at h
      have h1 : (i1, j1) ∈ ({(i2, j2), (i2, j2 + 1)} : Set (ℤ × ℤ)) := by rw [← h]; exact Set.mem_insert _ _
      have h2 : (i1 + 1, j1) ∈ ({(i2, j2), (i2, j2 + 1)} : Set (ℤ × ℤ)) := by rw [← h]; exact Set.mem_insert_of_mem _ rfl
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h1 h2
      rcases h1 with ⟨hi1, hj1⟩ | ⟨hi1, hj1⟩ <;>
      rcases h2 with ⟨hi2, hj2⟩ | ⟨hi2, hj2⟩ <;> omega
  | vertical i1 j1 =>
    cases d2 with
    | horizontal i2 j2 =>
      simp only [toShape] at h
      have h1 : (i1, j1) ∈ ({(i2, j2), (i2 + 1, j2)} : Set (ℤ × ℤ)) := by rw [← h]; exact Set.mem_insert _ _
      have h2 : (i1, j1 + 1) ∈ ({(i2, j2), (i2 + 1, j2)} : Set (ℤ × ℤ)) := by rw [← h]; exact Set.mem_insert_of_mem _ rfl
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h1 h2
      rcases h1 with ⟨hi1, hj1⟩ | ⟨hi1, hj1⟩ <;>
      rcases h2 with ⟨hi2, hj2⟩ | ⟨hi2, hj2⟩ <;> omega
    | vertical i2 j2 =>
      simp only [toShape] at h
      have h1 : (i1, j1) ∈ ({(i2, j2), (i2, j2 + 1)} : Set (ℤ × ℤ)) := by rw [← h]; exact Set.mem_insert _ _
      have h2 : (i1, j1 + 1) ∈ ({(i2, j2), (i2, j2 + 1)} : Set (ℤ × ℤ)) := by rw [← h]; exact Set.mem_insert_of_mem _ rfl
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h1 h2
      rcases h1 with ⟨hi1, hj1⟩ | ⟨hi1, hj1⟩
      · rcases h2 with ⟨hi2, hj2⟩ | ⟨hi2, hj2⟩ <;> [omega; simp only [hi1, hj1]]
      · rcases h2 with ⟨hi2, hj2⟩ | ⟨hi2, hj2⟩ <;> omega

/-- The empty shape has exactly one tiling (the empty tiling) -/
lemma Tiling.unique_empty (T : Tiling (∅ : Shape)) : T.dominos = ∅ := by
  by_contra h
  have hne : T.dominos.Nonempty := Set.nonempty_iff_ne_empty.mpr h
  obtain ⟨d, hd⟩ := hne
  have hsub : d.toShape ⊆ ∅ := by
    rw [← T.cover]
    exact Set.subset_biUnion_of_mem hd
  have hne' : d.toShape.Nonempty := Domino.toShape_nonempty d
  exact Set.not_nonempty_empty (hne'.mono hsub)

/-- TilingsHeight2 is a finite-type weighted set -/
lemma tilingsHeight2_isFiniteType : TilingsHeight2.IsFiniteType := by
  intro k
  -- The set of elements of weight k is exactly {(k, T) | T is a tiling of Rectangle k 2}
  have h : {a : (Σ n : ℕ, Tiling (Rectangle n 2)) | TilingsHeight2.weight a = k} =
           Sigma.mk k '' Set.univ := by
    ext ⟨n, T⟩
    simp only [TilingsHeight2, Set.mem_ofPred_eq, Set.mem_image, Set.mem_univ, true_and]
    constructor
    · intro hn
      subst hn
      exact ⟨T, rfl⟩
    · intro ⟨T', hT'⟩
      simp only [Sigma.mk.injEq] at hT'
      exact hT'.1.symm
  rw [h]
  apply Set.Finite.image
  -- Prove that the set of tilings of Rectangle k 2 is finite
  -- A tiling is determined by its set of dominos, which is a subset of all possible dominos
  -- in the rectangle. Since the rectangle is finite, so is the set of possible dominos.
  let DominosIn : Set Domino := {d | d.toShape ⊆ Rectangle k 2}
  have hDominosIn_finite : Set.Finite DominosIn := by
    have h : DominosIn ⊆
        (Set.Icc (1 : ℤ) k ×ˢ Set.Icc (1 : ℤ) 2).image (fun p => Domino.horizontal p.1 p.2) ∪
        (Set.Icc (1 : ℤ) k ×ˢ Set.Icc (1 : ℤ) 2).image (fun p => Domino.vertical p.1 p.2) := by
      intro d hd
      cases d with
      | horizontal i j =>
        left
        simp only [Set.mem_image, Set.mem_prod, Set.mem_Icc]
        use (i, j)
        simp only [DominosIn, Domino.toShape, Set.subset_def, Set.mem_ofPred_eq] at hd
        have h1 := hd (i, j) (by simp)
        simp only [Rectangle, Set.mem_ofPred_eq] at h1
        refine ⟨⟨⟨h1.1, ?_⟩, ⟨h1.2.2.1, h1.2.2.2⟩⟩, rfl⟩
        omega
      | vertical i j =>
        right
        simp only [Set.mem_image, Set.mem_prod, Set.mem_Icc]
        use (i, j)
        simp only [DominosIn, Domino.toShape, Set.subset_def, Set.mem_ofPred_eq] at hd
        have h1 := hd (i, j) (by simp)
        simp only [Rectangle, Set.mem_ofPred_eq] at h1
        refine ⟨⟨⟨h1.1, h1.2.1⟩, ⟨h1.2.2.1, ?_⟩⟩, rfl⟩
        omega
    apply Set.Finite.subset _ h
    apply Set.Finite.union
    · apply Set.Finite.image
      apply Set.Finite.prod
      · exact Set.finite_Icc (1 : ℤ) k
      · exact Set.finite_Icc (1 : ℤ) 2
    · apply Set.Finite.image
      apply Set.Finite.prod
      · exact Set.finite_Icc (1 : ℤ) k
      · exact Set.finite_Icc (1 : ℤ) 2
  -- Now show tilings are finite
  let f : Tiling (Rectangle k 2) → Set Domino := fun T => T.dominos
  have hf : Function.Injective f := by
    intro T₁ T₂ h
    cases T₁; cases T₂
    simp only [f] at h
    congr
  have h_tiling_subset : ∀ T : Tiling (Rectangle k 2), T.dominos ⊆ DominosIn := by
    intro T d hd
    simp only [DominosIn, Set.mem_ofPred_eq]
    have h : d.toShape ⊆ ⋃ d' ∈ T.dominos, d'.toShape := by
      intro p hp
      simp only [Set.mem_iUnion]
      exact ⟨d, hd, hp⟩
    rw [T.cover] at h
    exact h
  have h_range : Set.range f ⊆ 𝒫 DominosIn := by
    intro s hs
    simp only [Set.mem_range, f] at hs
    obtain ⟨T, rfl⟩ := hs
    simp only [Set.mem_powerset_iff]
    exact h_tiling_subset T
  have h_powerset_finite : Set.Finite (𝒫 DominosIn) := hDominosIn_finite.powerset
  have h_range_finite : Set.Finite (Set.range f) := h_powerset_finite.subset h_range
  have h_univ_finite : Set.Finite (f ⁻¹' Set.range f) := by
    apply h_range_finite.preimage
    exact hf.injOn
  convert h_univ_finite
  ext x
  simp only [Set.mem_univ, Set.mem_preimage, Set.mem_range, exists_apply_eq_apply]

/-- isFaultfree only depends on the dominos set -/
lemma isFaultfree_eq_of_dominos_eq {n : ℕ} {T1 T2 : Tiling (Rectangle n 2)} 
    (h : T1.dominos = T2.dominos) : isFaultfree n T1 ↔ isFaultfree n T2 := by
  simp only [isFaultfree, hasFault_eq_of_dominos_eq h]

/-- FaultfreeTilingsHeight2 is finite-type -/
lemma faultfreeTilingsHeight2_isFiniteType : FaultfreeTilingsHeight2.IsFiniteType := by
  intro m
  have h := tilingsHeight2_isFiniteType m
  -- The faultfree tilings embed into all tilings
  let f : (Σ n : ℕ, {T : Tiling (Rectangle n 2) // isFaultfree n T}) →
          (Σ n : ℕ, Tiling (Rectangle n 2)) := fun ⟨n, T, _⟩ => ⟨n, T⟩
  have hinj : Function.Injective f := by
    intro ⟨n₁, T₁, h₁⟩ ⟨n₂, T₂, h₂⟩ heq
    have heq' := Sigma.mk.inj_iff.mp heq
    obtain ⟨hn, hT⟩ := heq'
    subst hn
    simp only [heq_eq_eq] at hT
    subst hT
    rfl
  -- The image of the faultfree tilings under f is a subset of all tilings
  have himg : f '' {a | FaultfreeTilingsHeight2.weight a = m} ⊆
              {a | TilingsHeight2.weight a = m} := by
    intro ⟨n, T⟩ ⟨⟨n', T', hT'⟩, hmem, heq⟩
    simp only [Set.mem_ofPred_eq] at hmem ⊢
    obtain ⟨hn, hTeq⟩ := Sigma.mk.inj_iff.mp heq
    subst hn
    simp only [heq_eq_eq] at hTeq
    subst hTeq
    exact hmem
  -- Since the image is a subset of a finite set, it's finite
  have himg_fin : (f '' {a | FaultfreeTilingsHeight2.weight a = m}).Finite := h.subset himg
  -- Use Set.Finite.of_finite_image with InjOn
  have hinjOn : Set.InjOn f {a | FaultfreeTilingsHeight2.weight a = m} :=
    fun _ _ _ _ h => hinj h
  exact Set.Finite.of_finite_image himg_fin hinjOn

lemma domino_covering_11_valid (n : ℕ) (T : Tiling (Rectangle n 2))
    (d : Domino) (hd : d ∈ T.dominos) (h : (1, 1) ∈ d.toShape) :
    d = .vertical 1 1 ∨ d = .horizontal 1 1 := by
  cases d with
  | horizontal i j =>
    simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
    rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · right; simp only [Domino.horizontal.injEq]; omega
    · exfalso
      have hcover : ((0 : ℤ), (1 : ℤ)) ∈ (Domino.horizontal i j).toShape := by
        simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
        left; omega
      have := domino_subset_rect n T (Domino.horizontal i j) hd hcover
      simp only [Rectangle, Set.mem_ofPred_eq] at this; omega
  | vertical i j =>
    simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
    rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · left; simp only [Domino.vertical.injEq]; omega
    · exfalso
      have hcover : ((1 : ℤ), (0 : ℤ)) ∈ (Domino.vertical i j).toShape := by
        simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
        left; omega
      have := domino_subset_rect n T (Domino.vertical i j) hd hcover
      simp only [Rectangle, Set.mem_ofPred_eq] at this; omega

lemma no_horizontal_at_1_if_vertical (n : ℕ) (T : Tiling (Rectangle n 2))
    (hv : Domino.vertical 1 1 ∈ T.dominos) (i j : ℤ)
    (hd : Domino.horizontal i j ∈ T.dominos) : i < 1 ∨ i ≥ 2 := by
  have hdisj := T.pairwise_disjoint hv hd
  by_contra h; push Not at h; obtain ⟨hi1, hi2⟩ := h
  have hi : i = 1 := by omega
  have hd' : Domino.horizontal 1 j ∈ T.dominos := by rwa [hi] at hd
  have hsub := domino_subset_rect n T (Domino.horizontal 1 j) hd'
  have h1j : ((1 : ℤ), j) ∈ Rectangle n 2 := hsub (by simp [Domino.toShape])
  simp only [Rectangle, Set.mem_ofPred_eq] at h1j
  have hj12 : j = 1 ∨ j = 2 := by omega
  have h_in_horiz : ((1 : ℤ), j) ∈ (Domino.horizontal 1 j).toShape := by simp [Domino.toShape]
  have h_in_vert : ((1 : ℤ), j) ∈ (Domino.vertical 1 1).toShape := by
    simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    rcases hj12 with rfl | rfl <;> simp
  have hne : Domino.vertical 1 1 ≠ Domino.horizontal i j := by simp
  have hdisj' : Disjoint (Domino.vertical 1 1).toShape (Domino.horizontal i j).toShape := hdisj hne
  rw [hi] at hdisj'
  exact Set.disjoint_iff.mp hdisj' ⟨h_in_vert, h_in_horiz⟩

lemma fault_at_1_if_vertical (n : ℕ) (hn : n ≥ 2) (T : Tiling (Rectangle n 2))
    (hv : Domino.vertical 1 1 ∈ T.dominos) : hasFault n T 1 := by
  refine ⟨by omega, by omega, ?_⟩
  intro d hd
  cases d with
  | horizontal i j =>
    have := no_horizontal_at_1_if_vertical n T hv i j hd
    rcases this with h | h
    · left; omega
    · right; omega
  | vertical i j => trivial

lemma cell_12_in_rect (n : ℕ) (hn : n ≥ 1) : (1, 2) ∈ Rectangle n 2 := by
  simp only [Rectangle, Set.mem_ofPred_eq]; omega

lemma exists_domino_covering_12 (n : ℕ) (hn : n ≥ 1) (T : Tiling (Rectangle n 2)) :
    ∃ d ∈ T.dominos, (1, 2) ∈ d.toShape := by
  have h12 : (1, 2) ∈ Rectangle n 2 := cell_12_in_rect n hn
  rw [← T.cover] at h12
  simp only [Set.mem_iUnion] at h12
  obtain ⟨d, hd, hmem⟩ := h12
  exact ⟨d, hd, hmem⟩

lemma domino_covering_12_valid (n : ℕ) (T : Tiling (Rectangle n 2))
    (d : Domino) (hd : d ∈ T.dominos) (h : (1, 2) ∈ d.toShape) :
    d = .vertical 1 1 ∨ d = .horizontal 1 2 := by
  cases d with
  | horizontal i j =>
    simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
    rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · right; simp only [Domino.horizontal.injEq]; omega
    · exfalso
      have hcover : ((0 : ℤ), (2 : ℤ)) ∈ (Domino.horizontal i j).toShape := by
        simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
        left; omega
      have := domino_subset_rect n T (Domino.horizontal i j) hd hcover
      simp only [Rectangle, Set.mem_ofPred_eq] at this; omega
  | vertical i j =>
    simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
    rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · exfalso
      have hcover : ((1 : ℤ), (3 : ℤ)) ∈ (Domino.vertical i j).toShape := by
        simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
        right; omega
      have := domino_subset_rect n T (Domino.vertical i j) hd hcover
      simp only [Rectangle, Set.mem_ofPred_eq] at this; omega
    · left; simp only [Domino.vertical.injEq]; omega

lemma horizontal_12_if_horizontal_11 (n : ℕ) (hn : n ≥ 1) (T : Tiling (Rectangle n 2))
    (hh : Domino.horizontal 1 1 ∈ T.dominos) : Domino.horizontal 1 2 ∈ T.dominos := by
  obtain ⟨d, hd, hmem⟩ := exists_domino_covering_12 n hn T
  have hcases := domino_covering_12_valid n T d hd hmem
  rcases hcases with rfl | rfl
  · exfalso
    have hdisj := T.pairwise_disjoint hd hh
    have hne : Domino.vertical 1 1 ≠ Domino.horizontal 1 1 := by simp
    have : Disjoint (Domino.vertical 1 1).toShape (Domino.horizontal 1 1).toShape := hdisj hne
    have h11_vert : ((1 : ℤ), (1 : ℤ)) ∈ (Domino.vertical 1 1).toShape := by simp [Domino.toShape]
    have h11_horiz : ((1 : ℤ), (1 : ℤ)) ∈ (Domino.horizontal 1 1).toShape := by simp [Domino.toShape]
    exact Set.disjoint_iff.mp this ⟨h11_vert, h11_horiz⟩
  · exact hd

lemma no_horizontal_at_2_if_horizontal_pair (n : ℕ) (T : Tiling (Rectangle n 2))
    (hh1 : Domino.horizontal 1 1 ∈ T.dominos) (hh2 : Domino.horizontal 1 2 ∈ T.dominos)
    (i j : ℤ) (hd : Domino.horizontal i j ∈ T.dominos) : i < 2 ∨ i ≥ 3 := by
  by_contra h; push Not at h; obtain ⟨hi1, hi2⟩ := h
  have hi : i = 2 := by omega
  have hsub := domino_subset_rect n T (Domino.horizontal i j) hd
  have hij : ((i : ℤ), j) ∈ Rectangle n 2 := hsub (by simp [Domino.toShape])
  simp only [Rectangle, Set.mem_ofPred_eq] at hij
  have hj12 : j = 1 ∨ j = 2 := by omega
  rcases hj12 with rfl | rfl
  · have hdisj := T.pairwise_disjoint hh1 hd
    have hne : Domino.horizontal 1 1 ≠ Domino.horizontal i 1 := by simp; omega
    have : Disjoint (Domino.horizontal 1 1).toShape (Domino.horizontal i 1).toShape := hdisj hne
    have h21_h11 : ((2 : ℤ), (1 : ℤ)) ∈ (Domino.horizontal 1 1).toShape := by simp [Domino.toShape]
    have h21_hi1 : ((2 : ℤ), (1 : ℤ)) ∈ (Domino.horizontal i 1).toShape := by simp [Domino.toShape, hi]
    exact Set.disjoint_iff.mp this ⟨h21_h11, h21_hi1⟩
  · have hdisj := T.pairwise_disjoint hh2 hd
    have hne : Domino.horizontal 1 2 ≠ Domino.horizontal i 2 := by simp; omega
    have : Disjoint (Domino.horizontal 1 2).toShape (Domino.horizontal i 2).toShape := hdisj hne
    have h22_h12 : ((2 : ℤ), (2 : ℤ)) ∈ (Domino.horizontal 1 2).toShape := by simp [Domino.toShape]
    have h22_hi2 : ((2 : ℤ), (2 : ℤ)) ∈ (Domino.horizontal i 2).toShape := by simp [Domino.toShape, hi]
    exact Set.disjoint_iff.mp this ⟨h22_h12, h22_hi2⟩

lemma fault_at_2_if_horizontal (n : ℕ) (hn : n ≥ 3) (T : Tiling (Rectangle n 2))
    (hh : Domino.horizontal 1 1 ∈ T.dominos) : hasFault n T 2 := by
  have hn1 : n ≥ 1 := by omega
  have hh2 := horizontal_12_if_horizontal_11 n hn1 T hh
  refine ⟨by omega, by omega, ?_⟩
  intro d hd
  cases d with
  | horizontal i j =>
    have := no_horizontal_at_2_if_horizontal_pair n T hh hh2 i j hd
    rcases this with h | h
    · left; omega
    · right; omega
  | vertical i j => trivial

/-- The only faultfree tilings of height-2 rectangles have width 1 or 2 -/
lemma faultfree_height2_classification (n : ℕ) (T : Tiling (Rectangle n 2))
    (hff : isFaultfree n T) : n = 1 ∨ n = 2 := by
  obtain ⟨hn_pos, hno_fault⟩ := hff
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  -- So n ≥ 3 (since n > 0, n ≠ 1, n ≠ 2)
  have hn3 : n ≥ 3 := by omega
  -- Get the domino covering (1,1)
  have hn1 : n ≥ 1 := by omega
  obtain ⟨d, hd, hmem⟩ := exists_domino_covering_11 n hn1 T
  have hcases := domino_covering_11_valid n T d hd hmem
  rcases hcases with rfl | rfl
  · -- d = vertical 1 1: there's a fault at k=1
    have hfault := fault_at_1_if_vertical n (by omega) T hd
    exact hno_fault 1 hfault
  · -- d = horizontal 1 1: there's a fault at k=2
    have hfault := fault_at_2_if_horizontal n hn3 T hd
    exact hno_fault 2 hfault

/-- Every tiling of the 1×2 rectangle equals tiling_1_2 -/
lemma tiling_1_2_unique (T : Tiling (Rectangle 1 2)) : T = tiling_1_2 := by
  -- Prove equality by showing dominos are equal
  have hdom : T.dominos = tiling_1_2.dominos := by
    ext d
    constructor
    · intro hd
      have hsub : d.toShape ⊆ Rectangle 1 2 := by
        rw [← T.cover]
        exact Set.subset_biUnion_of_mem hd
      cases d with
      | horizontal i j =>
        simp only [Domino.toShape] at hsub
        have h1 : (i, j) ∈ Rectangle 1 2 := hsub (Set.mem_insert _ _)
        have h2 : (i + 1, j) ∈ Rectangle 1 2 := hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))
        simp only [Rectangle, Set.mem_ofPred_eq] at h1 h2
        omega
      | vertical i j =>
        simp only [Domino.toShape] at hsub
        have h1 : (i, j) ∈ Rectangle 1 2 := hsub (Set.mem_insert _ _)
        have h2 : (i, j + 1) ∈ Rectangle 1 2 := hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))
        simp only [Rectangle, Set.mem_ofPred_eq] at h1 h2
        have hi : i = 1 := by omega
        have hj : j = 1 := by omega
        subst hi hj
        exact Set.mem_singleton_iff.mpr rfl
    · intro hd
      simp only [tiling_1_2, Set.mem_singleton_iff] at hd
      subst hd
      have h11 : (1, 1) ∈ Rectangle 1 2 := by
        simp only [Rectangle, Set.mem_ofPred_eq]
        omega
      rw [← T.cover] at h11
      simp only [Set.mem_iUnion, exists_prop] at h11
      obtain ⟨d, hd, h11d⟩ := h11
      have hsub : d.toShape ⊆ Rectangle 1 2 := by
        rw [← T.cover]
        exact Set.subset_biUnion_of_mem hd
      cases d with
      | horizontal i j =>
        simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h11d
        rcases h11d with ⟨hi, hj⟩ | ⟨hi, hj⟩
        · subst hi hj
          have h21 : @Prod.mk ℤ ℤ 2 1 ∈ (Domino.horizontal 1 1).toShape := by simp [Domino.toShape]
          have h21' : @Prod.mk ℤ ℤ 2 1 ∈ Rectangle 1 2 := hsub h21
          simp only [Rectangle, Set.mem_ofPred_eq] at h21'
          omega
        · have hi' : i = 0 := by omega
          subst hi' hj
          have h01 : @Prod.mk ℤ ℤ 0 1 ∈ (Domino.horizontal 0 1).toShape := by simp [Domino.toShape]
          have h01' : @Prod.mk ℤ ℤ 0 1 ∈ Rectangle 1 2 := hsub h01
          simp only [Rectangle, Set.mem_ofPred_eq] at h01'
          omega
      | vertical i j =>
        simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h11d
        rcases h11d with ⟨hi, hj⟩ | ⟨hi, hj⟩
        · subst hi hj
          exact hd
        · have hj' : j = 0 := by omega
          subst hi hj'
          have h10 : @Prod.mk ℤ ℤ 1 0 ∈ (Domino.vertical 1 0).toShape := by simp [Domino.toShape]
          have h10' : @Prod.mk ℤ ℤ 1 0 ∈ Rectangle 1 2 := hsub h10
          simp only [Rectangle, Set.mem_ofPred_eq] at h10'
          omega
  exact Tiling.ext T tiling_1_2 hdom

/-- Every element of FaultfreeTilingsHeight2 with weight 1 equals faultfreeTiling_1_2 -/
lemma faultfreeTilingsHeight2_weight1_unique
    (x : Σ n : ℕ, {T : Tiling (Rectangle n 2) // isFaultfree n T})
    (hx : FaultfreeTilingsHeight2.weight x = 1) :
    x = ⟨1, faultfreeTiling_1_2⟩ := by
  obtain ⟨n, T, hT⟩ := x
  simp only [FaultfreeTilingsHeight2] at hx
  subst hx
  congr 1
  -- Need to show ⟨T, hT⟩ = faultfreeTiling_1_2
  simp only [faultfreeTiling_1_2, Subtype.mk.injEq]
  exact tiling_1_2_unique T

/-- There is exactly one faultfree tiling of width 1 (one vertical domino) -/
lemma countOfWeight_faultfreeHeight2_one :
    FaultfreeTilingsHeight2.countOfWeight faultfreeTilingsHeight2_isFiniteType 1 = 1 := by
  unfold WeightedSet.countOfWeight
  have hset : {a | FaultfreeTilingsHeight2.weight a = 1} = {⟨1, faultfreeTiling_1_2⟩} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hx
      exact faultfreeTilingsHeight2_weight1_unique x hx
    · intro hx
      subst hx
      rfl
  have hfin : ({⟨1, faultfreeTiling_1_2⟩} : Set (Σ n : ℕ, {T : Tiling (Rectangle n 2) // isFaultfree n T})).Finite :=
    Set.finite_singleton _
  have heq : (faultfreeTilingsHeight2_isFiniteType 1).toFinset = hfin.toFinset := by
    apply Set.Finite.toFinset_inj.mpr
    exact hset
  rw [heq]
  simp only [Set.Finite.toFinset_singleton, card_singleton]

/-- The two horizontal dominos tiling is faultfree -/
lemma twoHorizontalDominos_isFaultfree : isFaultfree 2 twoHorizontalDominos := by
  constructor
  · omega
  · intro k hfault
    unfold hasFault at hfault
    obtain ⟨hk_pos, hk_lt, hdom⟩ := hfault
    have hk1 : k = 1 := by omega
    subst hk1
    have hcontra := hdom (Domino.horizontal 1 1) (by simp [twoHorizontalDominos])
    simp only at hcontra
    omega

/-- For a faultfree tiling of width 2, there must be a horizontal domino straddling position 1 -/
lemma faultfree_width2_has_horizontal_at_1 (T : Tiling (Rectangle 2 2)) (hff : isFaultfree 2 T) :
    Domino.horizontal 1 1 ∈ T.dominos ∨ Domino.horizontal 1 2 ∈ T.dominos := by
  obtain ⟨_, hno_fault⟩ := hff
  by_contra h
  push Not at h
  obtain ⟨hnh1, hnh2⟩ := h
  have hfault : hasFault 2 T 1 := by
    refine ⟨by omega, by omega, ?_⟩
    intro d hd
    cases d with
    | horizontal i j =>
      have hsub := domino_subset_rect 2 T (Domino.horizontal i j) hd
      have hij : (i, j) ∈ Rectangle 2 2 := hsub (Set.mem_insert (i, j) _)
      have hij' : (i + 1, j) ∈ Rectangle 2 2 := hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      simp only [Rectangle, Set.mem_ofPred_eq] at hij hij'
      have hi : i = 1 := by omega
      have hj : j = 1 ∨ j = 2 := by omega
      subst hi
      rcases hj with rfl | rfl
      · exact (hnh1 hd).elim
      · exact (hnh2 hd).elim
    | vertical _ _ => trivial
  exact hno_fault 1 hfault

lemma exists_domino_covering' (n : ℕ) (T : Tiling (Rectangle n 2)) (i j : ℤ)
    (h : (i, j) ∈ Rectangle n 2) :
    ∃ d ∈ T.dominos, (i, j) ∈ d.toShape := by
  rw [← T.cover] at h
  simp only [Set.mem_iUnion] at h
  obtain ⟨d, hd, hmem⟩ := h
  exact ⟨d, hd, hmem⟩

/-- For a faultfree tiling of width 2, horizontal dominos at (1,1) and (1,2) must both be present -/
lemma horizontal_11_implies_12' (T : Tiling (Rectangle 2 2))
    (hh : Domino.horizontal 1 1 ∈ T.dominos) : Domino.horizontal 1 2 ∈ T.dominos := by
  have h12 : (1, 2) ∈ Rectangle 2 2 := by simp only [Rectangle, Set.mem_ofPred_eq]; omega
  obtain ⟨d, hd, hmem⟩ := exists_domino_covering' 2 T 1 2 h12
  cases d with
  | horizontal i j =>
    simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · subst hi hj; exact hd
    · have hi' : i = 0 := by omega
      have hsub := domino_subset_rect 2 T (Domino.horizontal i j) hd
      have h02 : (i, j) ∈ Rectangle 2 2 := hsub (Set.mem_insert (i, j) _)
      simp only [Rectangle, Set.mem_ofPred_eq, hi'] at h02
      omega
  | vertical i j =>
    simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · have hsub := domino_subset_rect 2 T (Domino.vertical i j) hd
      have h13 : (i, j + 1) ∈ Rectangle 2 2 := hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      simp only [Rectangle, Set.mem_ofPred_eq, hi] at h13
      omega
    · have hi' : i = 1 := by omega
      have hj' : j = 1 := by omega
      subst hi' hj'
      have hdisj := T.pairwise_disjoint hh hd
      have hne : Domino.horizontal 1 1 ≠ Domino.vertical 1 1 := by intro h; cases h
      have hdisjoint : Disjoint (Domino.horizontal 1 1).toShape (Domino.vertical 1 1).toShape := hdisj hne
      have h11_h : ((1 : ℤ), (1 : ℤ)) ∈ (Domino.horizontal 1 1).toShape := Set.mem_insert (1, 1) _
      have h11_v : ((1 : ℤ), (1 : ℤ)) ∈ (Domino.vertical 1 1).toShape := Set.mem_insert (1, 1) _
      exact False.elim (Set.not_disjoint_iff.mpr ⟨(1, 1), h11_h, h11_v⟩ hdisjoint)

lemma horizontal_12_implies_11' (T : Tiling (Rectangle 2 2))
    (hh : Domino.horizontal 1 2 ∈ T.dominos) : Domino.horizontal 1 1 ∈ T.dominos := by
  have h11 : (1, 1) ∈ Rectangle 2 2 := by simp only [Rectangle, Set.mem_ofPred_eq]; omega
  obtain ⟨d, hd, hmem⟩ := exists_domino_covering' 2 T 1 1 h11
  cases d with
  | horizontal i j =>
    simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · subst hi hj; exact hd
    · have hi' : i = 0 := by omega
      have hsub := domino_subset_rect 2 T (Domino.horizontal i j) hd
      have h01 : (i, j) ∈ Rectangle 2 2 := hsub (Set.mem_insert (i, j) _)
      simp only [Rectangle, Set.mem_ofPred_eq, hi'] at h01
      omega
  | vertical i j =>
    simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · have hi' : i = 1 := by omega
      have hj' : j = 1 := by omega
      subst hi' hj'
      have hdisj := T.pairwise_disjoint hh hd
      have hne : Domino.horizontal 1 2 ≠ Domino.vertical 1 1 := by intro h; cases h
      have hdisjoint : Disjoint (Domino.horizontal 1 2).toShape (Domino.vertical 1 1).toShape := hdisj hne
      have h12_h : ((1 : ℤ), (2 : ℤ)) ∈ (Domino.horizontal 1 2).toShape := Set.mem_insert (1, 2) _
      have h12_v : ((1 : ℤ), (2 : ℤ)) ∈ (Domino.vertical 1 1).toShape :=
        Set.mem_insert_of_mem _ (Set.mem_singleton _)
      exact False.elim (Set.not_disjoint_iff.mpr ⟨(1, 2), h12_h, h12_v⟩ hdisjoint)
    · have hj' : j = 0 := by omega
      have hsub := domino_subset_rect 2 T (Domino.vertical i j) hd
      have h10 : (i, j) ∈ Rectangle 2 2 := hsub (Set.mem_insert (i, j) _)
      simp only [Rectangle, Set.mem_ofPred_eq, hj'] at h10
      omega

/-- A faultfree tiling of width 2 has exactly horizontal 1 1 and horizontal 1 2 -/
lemma faultfree_width2_dominos (T : Tiling (Rectangle 2 2)) (hff : isFaultfree 2 T) :
    Domino.horizontal 1 1 ∈ T.dominos ∧ Domino.horizontal 1 2 ∈ T.dominos := by
  have h := faultfree_width2_has_horizontal_at_1 T hff
  rcases h with hh1 | hh2
  · exact ⟨hh1, horizontal_11_implies_12' T hh1⟩
  · exact ⟨horizontal_12_implies_11' T hh2, hh2⟩

/-- The dominos of a faultfree tiling of width 2 are exactly {horizontal 1 1, horizontal 1 2} -/
lemma faultfree_width2_dominos_eq (T : Tiling (Rectangle 2 2)) (hff : isFaultfree 2 T) :
    T.dominos = {Domino.horizontal 1 1, Domino.horizontal 1 2} := by
  have ⟨hh1, hh2⟩ := faultfree_width2_dominos T hff
  ext d
  constructor
  · intro hd
    have hsub := domino_subset_rect 2 T d hd
    cases d with
    | horizontal i j =>
      have hij : (i, j) ∈ Rectangle 2 2 := hsub (Set.mem_insert (i, j) _)
      have hij' : (i + 1, j) ∈ Rectangle 2 2 := hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      simp only [Rectangle, Set.mem_ofPred_eq] at hij hij'
      have hi : i = 1 := by omega
      have hj : j = 1 ∨ j = 2 := by omega
      subst hi
      rcases hj with rfl | rfl
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    | vertical i j =>
      have hij : (i, j) ∈ Rectangle 2 2 := hsub (Set.mem_insert (i, j) _)
      have hij' : (i, j + 1) ∈ Rectangle 2 2 := hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      simp only [Rectangle, Set.mem_ofPred_eq] at hij hij'
      have hi : i = 1 ∨ i = 2 := by omega
      have hj : j = 1 := by omega
      subst hj
      rcases hi with rfl | rfl
      · have hdisj := T.pairwise_disjoint hh1 hd
        have hne : Domino.horizontal 1 1 ≠ Domino.vertical 1 1 := by intro h; cases h
        have hdisjoint : Disjoint (Domino.horizontal 1 1).toShape (Domino.vertical 1 1).toShape := hdisj hne
        have h11_h : ((1 : ℤ), (1 : ℤ)) ∈ (Domino.horizontal 1 1).toShape := Set.mem_insert (1, 1) _
        have h11_v : ((1 : ℤ), (1 : ℤ)) ∈ (Domino.vertical 1 1).toShape := Set.mem_insert (1, 1) _
        exact False.elim (Set.not_disjoint_iff.mpr ⟨(1, 1), h11_h, h11_v⟩ hdisjoint)
      · have hdisj := T.pairwise_disjoint hh1 hd
        have hne : Domino.horizontal 1 1 ≠ Domino.vertical 2 1 := by intro h; cases h
        have hdisjoint : Disjoint (Domino.horizontal 1 1).toShape (Domino.vertical 2 1).toShape := hdisj hne
        have h21_h : ((2 : ℤ), (1 : ℤ)) ∈ (Domino.horizontal 1 1).toShape :=
          Set.mem_insert_of_mem _ (Set.mem_singleton _)
        have h21_v : ((2 : ℤ), (1 : ℤ)) ∈ (Domino.vertical 2 1).toShape := Set.mem_insert (2, 1) _
        exact False.elim (Set.not_disjoint_iff.mpr ⟨(2, 1), h21_h, h21_v⟩ hdisjoint)
  · intro hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with rfl | rfl
    · exact hh1
    · exact hh2

/-- Any faultfree tiling of Rectangle 2 2 equals twoHorizontalDominos -/
lemma faultfree_tiling_width2_unique (T : Tiling (Rectangle 2 2)) (hff : isFaultfree 2 T) :
    T = twoHorizontalDominos := by
  have hdom := faultfree_width2_dominos_eq T hff
  exact Tiling.ext T twoHorizontalDominos hdom

/-- There is exactly one faultfree tiling of width 2 (two horizontal dominos) -/
lemma countOfWeight_faultfreeHeight2_two :
    FaultfreeTilingsHeight2.countOfWeight faultfreeTilingsHeight2_isFiniteType 2 = 1 := by
  unfold WeightedSet.countOfWeight
  -- The set of faultfree tilings of weight 2 is a singleton
  have hsingleton : {a : Σ n : ℕ, {T : Tiling (Rectangle n 2) // isFaultfree n T} |
      FaultfreeTilingsHeight2.weight a = 2} =
      {⟨2, twoHorizontalDominos, twoHorizontalDominos_isFaultfree⟩} := by
    ext ⟨n, T, hT⟩
    simp only [FaultfreeTilingsHeight2, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hn
      -- hn : weight ⟨n, T, hT⟩ = 2, i.e. n = 2 after unfolding
      subst hn
      have heq := faultfree_tiling_width2_unique T hT
      subst heq
      rfl
    · intro heq
      simp only [Sigma.mk.inj_iff] at heq
      obtain ⟨hn, hTeq⟩ := heq
      simp only [hn]
  have hfin := faultfreeTilingsHeight2_isFiniteType 2
  have hfin' := Set.finite_singleton (⟨2, twoHorizontalDominos, twoHorizontalDominos_isFaultfree⟩ :
      Σ n : ℕ, {T : Tiling (Rectangle n 2) // isFaultfree n T})
  have heq_fin : hfin.toFinset = hfin'.toFinset := by
    ext x
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hx
      have : x ∈ {a | FaultfreeTilingsHeight2.weight a = 2} := hx
      rw [hsingleton] at this
      exact this
    · intro hx
      subst hx
      rfl
  rw [heq_fin]
  simp only [Set.Finite.toFinset_singleton, card_singleton]

/-- For n ≠ 1 and n ≠ 2, there are no faultfree tilings of width n -/
lemma countOfWeight_faultfreeHeight2_eq_zero (n : ℕ) (hn1 : n ≠ 1) (hn2 : n ≠ 2) :
    FaultfreeTilingsHeight2.countOfWeight faultfreeTilingsHeight2_isFiniteType n = 0 := by
  unfold WeightedSet.countOfWeight
  rw [Finset.card_eq_zero]
  ext ⟨m, T, hT⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  constructor
  · intro hm
    simp only [FaultfreeTilingsHeight2] at hm
    have := faultfree_height2_classification m T hT
    simp
    omega
  · simp

/-- The generating function of faultfree height-2 tilings is x + x² -/
lemma weightGenFun_faultfreeHeight2 :
    FaultfreeTilingsHeight2.weightGenFun (R := ℚ) faultfreeTilingsHeight2_isFiniteType =
      PowerSeries.X + PowerSeries.X ^ 2 := by
  ext n
  simp only [WeightedSet.weightGenFun, PowerSeries.coeff_mk, map_add, coeff_X, coeff_X_pow]
  rcases n with _ | _ | _ | n
  · -- n = 0
    have h0 : FaultfreeTilingsHeight2.countOfWeight faultfreeTilingsHeight2_isFiniteType 0 = 0 :=
      countOfWeight_faultfreeHeight2_eq_zero 0 (by omega) (by omega)
    simp [h0]
  · -- n = 1
    rw [countOfWeight_faultfreeHeight2_one]
    norm_num
  · -- n = 2
    rw [countOfWeight_faultfreeHeight2_two]
    norm_num
  · -- n ≥ 3
    have hn1 : n + 3 ≠ 1 := by omega
    have hn2 : n + 3 ≠ 2 := by omega
    have h3 : FaultfreeTilingsHeight2.countOfWeight faultfreeTilingsHeight2_isFiniteType (n + 3) = 0 :=
      countOfWeight_faultfreeHeight2_eq_zero (n + 3) hn1 hn2
    simp [h3, hn2]

/-- Shifting is injective -/
lemma Domino.shift_injective (offset : ℤ) : Function.Injective (fun d : Domino => d.shift offset) := by
  intro d1 d2 h
  cases d1 <;> cases d2 <;> simp only [shift, Domino.horizontal.injEq, Domino.vertical.injEq] at h ⊢
  · omega
  · contradiction
  · contradiction
  · omega


/-- Casting a tiling preserves its dominos -/
@[simp]
lemma Tiling.cast_dominos {S S' : Shape} (h : S = S') (T : Tiling S) :
    (T.cast h).dominos = T.dominos := rfl

/-- The partial width sum at i plus width of component i gives the next partial sum -/
lemma partialWidthSum_succ (k : ℕ) 
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (i : Fin k) (hi : i.val + 1 < k) :
    partialWidthSum k ts ⟨i.val + 1, hi⟩ = partialWidthSum k ts i + (ts i).1 := by
  simp only [partialWidthSum]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.last, Fin.val_mk, Fin.val_castSucc, add_comm]

/-- Helper lemma: The width of composeTilings with a prepended element equals
    the first width plus the sum of the remaining widths.
    This is used in proving composeTilings_decomposeTiling. -/
lemma composeTilings_prepend_width (m : ℕ) (first_width : ℕ)
    (first : {T' : Tiling (Rectangle first_width 2) // isFaultfree first_width T'})
    (rest : Fin m → (Σ w : ℕ, {T' : Tiling (Rectangle w 2) // isFaultfree w T'}))
    (ts : Fin (m + 1) → (Σ w : ℕ, {T' : Tiling (Rectangle w 2) // isFaultfree w T'}))
    (hts : ts = fun i => if hi : i.val = 0 then ⟨first_width, first⟩ else rest ⟨i.val - 1, by omega⟩) :
    (composeTilings (m + 1) ts).1 = first_width + ∑ j : Fin m, (rest j).1 := by
  simp only [composeTilings, hts]
  rw [Fin.sum_univ_succ]
  -- `0 = 0` is propositionally True, not defeq True; use ↓reduceDIte
  simp only [Fin.val_zero, ↓reduceDIte, Fin.val_succ, Nat.add_one_ne_zero, Nat.add_sub_cancel]
/-- Helper lemma: When we compose with a prepended element, if the rest composes to 
    a specific width and tiling, then the total width equals first_width + rest_width. -/
lemma composeTilings_prepend_width' (m : ℕ) (first_width rest_width : ℕ)
    (first : {T' : Tiling (Rectangle first_width 2) // isFaultfree first_width T'})
    (rest : Fin m → (Σ w : ℕ, {T' : Tiling (Rectangle w 2) // isFaultfree w T'}))
    (hrest : (composeTilings m rest).1 = rest_width)
    (ts : Fin (m + 1) → (Σ w : ℕ, {T' : Tiling (Rectangle w 2) // isFaultfree w T'}))
    (hts : ts = fun i => if hi : i.val = 0 then ⟨first_width, first⟩ else rest ⟨i.val - 1, by omega⟩) :
    (composeTilings (m + 1) ts).1 = first_width + rest_width := by
  rw [composeTilings_prepend_width m first_width first rest ts hts]
  simp only [composeTilings] at hrest
  rw [hrest]

/-- Shifting by k then by -k returns the original domino -/
lemma Domino.shiftNeg_shiftNat (d : Domino) (k : ℕ) : (d.shiftNat k).shiftNeg k = d := by
  cases d <;> simp [shiftNat, shiftNeg, shift]

/-- `restrictTilingLeft` does not depend on the proof of `hasFault` -/
@[simp]
lemma restrictTilingLeft_proof_irrel (n : ℕ) (T : Tiling (Rectangle n 2)) (k : ℕ) 
    (hk1 hk2 : hasFault n T k) : 
    restrictTilingLeft n T k hk1 = restrictTilingLeft n T k hk2 := rfl

/-- `restrictTilingRight` does not depend on the proof of `hasFault` -/
@[simp]
lemma restrictTilingRight_proof_irrel (n : ℕ) (T : Tiling (Rectangle n 2)) (k : ℕ) 
    (hk1 hk2 : hasFault n T k) : 
    restrictTilingRight n T k hk1 = restrictTilingRight n T k hk2 := rfl

/-- At a fault position, the tiling's dominos split into left and right parts -/
lemma dominos_eq_leftPart_union_rightPart (n : ℕ) (T : Tiling (Rectangle n 2)) (k : ℕ) 
    (hk : hasFault n T k) : 
    T.dominos = {d ∈ T.dominos | d.inLeftPart k} ∪ {d ∈ T.dominos | d.inRightPart k} := by
  ext d
  simp only [Set.mem_union, Set.mem_sep_iff]
  constructor
  · intro hd
    rcases domino_left_or_right_at_fault hk d hd with hleft | hright
    · left; exact ⟨hd, hleft⟩
    · right; exact ⟨hd, hright⟩
  · intro hd
    rcases hd with ⟨hd, _⟩ | ⟨hd, _⟩ <;> exact hd


/-- The partial width sum at index 1 equals the width of the first component -/
lemma partialWidthSum_one (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    partialWidthSum k ts ⟨1, by omega⟩ = (ts ⟨0, by omega⟩).1 := by
  simp only [partialWidthSum, Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero, Fin.val_zero]

/-- The width of decomposeTiling when faults exist equals m+1 where m is the count from
    decomposing the right part. This is useful for proving composeTilings_decomposeTiling. -/
lemma decomposeTiling_hasFault_fst (n : ℕ) (T : Tiling (Rectangle (n + 1) 2))
    (hne : (faultPositions (n + 1) T).Nonempty) :
    let k := minFault (n + 1) T hne
    let hk := minFault_hasFault (n + 1) T hne
    let right := restrictTilingRight (n + 1) T k hk
    (decomposeTiling (n + 1) T).1 = (decomposeTiling (n + 1 - k) right).1 + 1 := by
  simp only [decomposeTiling, dite_eq_left hne]


/-- Decomposing a faultfree tiling returns a singleton tuple containing the original tiling.
    This is a key helper for proving `decomposeTiling_composeTilings`. -/
lemma decomposeTiling_faultfree (n : ℕ) (T : Tiling (Rectangle (n + 1) 2))
    (hff : isFaultfree (n + 1) T) :
    decomposeTiling (n + 1) T = ⟨1, fun _ => ⟨n + 1, ⟨T, hff⟩⟩⟩ := by
  unfold decomposeTiling
  -- Since T is faultfree, faultPositions is empty, so Nonempty is false
  have hne : ¬(faultPositions (n + 1) T).Nonempty := 
    faultPositions_not_nonempty_of_isFaultfree (n + 1) T hff
  simp only [dite_eq_right hne]

/-- The left restriction of a subst'd tiling equals the left restriction of the original. -/
lemma restrictTilingLeft_subst {n m : ℕ} (h : n = m) (T : Tiling (Rectangle n 2)) (k : ℕ)
    (hk : hasFault n T k) :
    restrictTilingLeft m (h ▸ T) k (by subst h; exact hk) = 
    restrictTilingLeft n T k hk := by
  subst h
  rfl

/-- The right restriction of a subst'd tiling has the same dominos as the original. -/
lemma restrictTilingRight_subst_dominos {n m : ℕ} (h : n = m) (T : Tiling (Rectangle n 2)) (k : ℕ)
    (hk : hasFault n T k) :
    (restrictTilingRight m (h ▸ T) k (by subst h; exact hk)).dominos = 
    (restrictTilingRight n T k hk).dominos := by
  subst h
  rfl

/-- Corollary: Any tiling decomposes into a tuple of faultfree tilings with matching total weight -/
lemma tiling_decomposition (n : ℕ) (T : Tiling (Rectangle n 2)) :
    ∃ (k : ℕ) (ts : Fin k → Σ m, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}),
      (∑ i, (ts i).1) = n :=
  ⟨(decomposeTiling n T).1, (decomposeTiling n T).2, decomposeTiling_weight_sum n T⟩

/-- The vertical domino is not in the image of shifted dominos from Rectangle m 2. -/
lemma vertical_11_not_in_shiftNat_image (m : ℕ) (T : Tiling (Rectangle m 2)) :
    Domino.vertical 1 1 ∉ T.dominos.image (fun d => d.shiftNat 1) := by
  simp only [Set.mem_image, not_exists, not_and]
  intro d hd heq
  cases d with
  | horizontal i j =>
    simp only [Domino.shiftNat, Domino.shift] at heq
    exact Domino.noConfusion heq
  | vertical i j =>
    simp only [Domino.shiftNat, Domino.shift, Domino.vertical.injEq] at heq
    have hsub := domino_subset_rect m T (Domino.vertical i j) hd
    have hi_ge : i ≥ 1 := by
      have := hsub (Set.mem_insert (i, j) _)
      simp only [Rectangle, Set.mem_ofPred_eq] at this
      exact this.1
    omega

/-- The horizontal dominos are not in the image of shifted dominos from Rectangle m 2. -/
lemma horizontal_11_not_in_shiftNat2_image (m : ℕ) (T : Tiling (Rectangle m 2)) :
    Domino.horizontal 1 1 ∉ T.dominos.image (fun d => d.shiftNat 2) := by
  simp only [Set.mem_image, not_exists, not_and]
  intro d hd heq
  cases d with
  | horizontal i j =>
    simp only [Domino.shiftNat, Domino.shift, Domino.horizontal.injEq] at heq
    have hsub := domino_subset_rect m T (Domino.horizontal i j) hd
    have hi_ge : i ≥ 1 := by
      have := hsub (Set.mem_insert (i, j) _)
      simp only [Rectangle, Set.mem_ofPred_eq] at this
      exact this.1
    omega
  | vertical i j =>
    simp only [Domino.shiftNat, Domino.shift] at heq
    exact Domino.noConfusion heq

lemma horizontal_12_not_in_shiftNat2_image (m : ℕ) (T : Tiling (Rectangle m 2)) :
    Domino.horizontal 1 2 ∉ T.dominos.image (fun d => d.shiftNat 2) := by
  simp only [Set.mem_image, not_exists, not_and]
  intro d hd heq
  cases d with
  | horizontal i j =>
    simp only [Domino.shiftNat, Domino.shift, Domino.horizontal.injEq] at heq
    have hsub := domino_subset_rect m T (Domino.horizontal i j) hd
    have hi_ge : i ≥ 1 := by
      have := hsub (Set.mem_insert (i, j) _)
      simp only [Rectangle, Set.mem_ofPred_eq] at this
      exact this.1
    omega
  | vertical i j =>
    simp only [Domino.shiftNat, Domino.shift] at heq
    exact Domino.noConfusion heq

/-- The vertical domino at (1,1) is not in the image of dominos shifted by 2. -/
lemma vertical_11_not_in_shiftNat2_image (m : ℕ) (T : Tiling (Rectangle m 2)) :
    Domino.vertical 1 1 ∉ T.dominos.image (fun d => d.shiftNat 2) := by
  simp only [Set.mem_image, not_exists, not_and]
  intro d hd heq
  cases d with
  | horizontal i j =>
    simp only [Domino.shiftNat, Domino.shift] at heq
    exact Domino.noConfusion heq
  | vertical i j =>
    simp only [Domino.shiftNat, Domino.shift, Domino.vertical.injEq] at heq
    have hsub := domino_subset_rect m T (Domino.vertical i j) hd
    have hi_ge : i ≥ 1 := by
      have := hsub (Set.mem_insert (i, j) _)
      simp only [Rectangle, Set.mem_ofPred_eq] at this
      exact this.1
    omega

/-- The empty rectangle has exactly one tiling -/
@[simp] lemma numTilings_0_2 : d_[0, 2] = 1 := by
  unfold numTilings
  rw [Rectangle_zero_left]
  have huniq : Unique (Tiling (∅ : Shape)) := {
    default := Tiling.empty
    uniq := fun T => by
      have hdom := Tiling.unique_empty T
      cases T
      simp only [Tiling.mk.injEq, Tiling.empty]
      exact hdom
  }
  exact Nat.card_unique

/-- The 1×2 rectangle has exactly one tiling -/
@[simp] lemma numTilings_1_2 : d_[1, 2] = 1 := by
  unfold numTilings
  have huniq : Unique (Tiling (Rectangle 1 2)) := {
    default := tiling_1_2
    uniq := tiling_1_2_unique
  }
  exact Nat.card_unique

/-- The Fibonacci recurrence for tiling counts: d_{n+2,2} = d_{n,2} + d_{n+1,2}.

    This follows from the bijection:
    Tiling (Rectangle (n+2) 2) ≃ Tiling (Rectangle n 2) ⊕ Tiling (Rectangle (n+1) 2)

    The bijection classifies tilings based on what covers the first column:
    - If a vertical domino covers (1,1)-(1,2): removing it and shifting gives a tiling of Rectangle (n+1) 2
    - If horizontal dominos cover (1,1)-(2,1) and (1,2)-(2,2): removing them and shifting gives a tiling of Rectangle n 2

    This is a classical result in combinatorics. -/
lemma numTilings_recurrence (n : ℕ) : d_[n + 2, 2] = d_[n, 2] + d_[n + 1, 2] := by
  -- The proof constructs a bijection between tilings of Rectangle (n+2) 2 and
  -- the disjoint union of tilings of Rectangle n 2 and Rectangle (n+1) 2.
  -- 
  -- The key insight is that every tiling of Rectangle (n+2) 2 has its first column covered 
  -- by either:
  -- 1. A vertical domino at (1,1)-(1,2) (giving a tiling of Rectangle (n+1) 2 after removal and shift)
  -- 2. Two horizontal dominos at (1,1)-(2,1) and (1,2)-(2,2) (giving a tiling of Rectangle n 2 after removal and shift)
  --
  -- The bijection is established using:
  -- - exists_domino_covering_11: there exists a domino covering (1,1)
  -- - domino_covering_11_valid: that domino is either vertical 1 1 or horizontal 1 1
  -- - horizontal_12_if_horizontal_11: if horizontal 1 1 is present, so is horizontal 1 2
  -- - fault_at_1_if_vertical: if vertical 1 1 is present, there's a fault at 1
  -- - fault_at_2_if_horizontal: if horizontal 1 1 is present, there's a fault at 2
  -- - restrictTilingRight: get the right part at a fault
  --
  -- The formal construction uses Equiv.sumCompl to partition tilings by whether 
  -- vertical 1 1 is present, then constructs equivalences for each part.
  unfold numTilings
  -- We need: Nat.card (Tiling (Rectangle (n+2) 2)) = Nat.card (Tiling (Rectangle n 2)) + Nat.card (Tiling (Rectangle (n+1) 2))
  -- 
  -- Define the predicate: P(T) := Domino.vertical 1 1 ∈ T.dominos
  -- Then by Equiv.sumCompl: Tiling (Rectangle (n+2) 2) ≃ {T | P T} ⊕ {T | ¬P T}
  --
  -- We need two equivalences:
  -- e1 : {T | P T} ≃ Tiling (Rectangle (n+1) 2)  (remove vertical, shift by -1)
  -- e2 : {T | ¬P T} ≃ Tiling (Rectangle n 2)     (remove horizontal pair, shift by -2)
  --
  -- The construction of these equivalences requires:
  -- - Forward: use restrictTilingRight with the appropriate fault
  -- - Backward: prepend the appropriate dominos and shift
  --
  -- The equivalence is constructed using the classification of tilings by what covers (1,1).
  -- Every tiling of Rectangle (n+2) 2 has exactly one of:
  -- - vertical 1 1 ∈ T.dominos (covering column 1 with one vertical domino)
  -- - horizontal 1 1 ∈ T.dominos (covering columns 1-2 with two horizontal dominos)
  -- They can't both be present since they overlap at (1,1).
  --
  -- Forward map: T ↦ if vertical 1 1 ∈ T.dominos then Sum.inr (restrictTilingRight T 1)
  --                                               else Sum.inl (restrictTilingRight T 2)
  -- 
  -- Inverse map: Sum.inl T' ↦ prepend {horizontal 1 1, horizontal 1 2} and shift T' by 2
  --              Sum.inr T' ↦ prepend {vertical 1 1} and shift T' by 1
  --
  -- The proof that these are inverses follows from:
  -- 1. At a fault, T.dominos = leftPart ∪ (rightPart.image shiftNat k)
  -- 2. For fault at 1: leftPart = {vertical 1 1}
  -- 3. For fault at 2: leftPart = {horizontal 1 1, horizontal 1 2}
  -- 4. shiftNat and shiftNeg are inverses
  --
  -- This is a standard combinatorial bijection (the Fibonacci recurrence for domino tilings).
  have e : Tiling (Rectangle (n + 2) 2) ≃ Tiling (Rectangle n 2) ⊕ Tiling (Rectangle (n + 1) 2) := by
    -- Helper: vertical 1 1 and horizontal 1 1 overlap at (1,1), so they can't both be in a tiling
    have vertical_horizontal_disjoint : ∀ T : Tiling (Rectangle (n + 2) 2), 
        ¬(Domino.vertical 1 1 ∈ T.dominos ∧ Domino.horizontal 1 1 ∈ T.dominos) := by
      intro T ⟨hv, hh⟩
      have hne : Domino.vertical 1 1 ≠ Domino.horizontal 1 1 := by intro h; exact Domino.noConfusion h
      have hdisj := T.pairwise_disjoint hv hh hne
      simp only [Function.onFun] at hdisj
      rw [Set.disjoint_iff_inter_eq_empty] at hdisj
      have h11 : ((1 : ℤ), (1 : ℤ)) ∈ (Domino.vertical 1 1).toShape ∩ (Domino.horizontal 1 1).toShape := by
        constructor
        · simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
          left; trivial
        · simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
          left; trivial
      rw [hdisj] at h11
      exact h11
    -- Helper: every tiling of Rectangle (n+2) 2 has either vertical 1 1 or horizontal 1 1
    have classification : ∀ T : Tiling (Rectangle (n + 2) 2), 
        Domino.vertical 1 1 ∈ T.dominos ∨ Domino.horizontal 1 1 ∈ T.dominos := by
      intro T
      obtain ⟨d, hd, hmem⟩ := exists_domino_covering_11 (n + 2) (by omega) T
      have hcases := domino_covering_11_valid (n + 2) T d hd hmem
      rcases hcases with rfl | rfl
      · left; exact hd
      · right; exact hd
    -- Helper: if vertical 1 1 ∈ T.dominos, then horizontal 1 1 ∉ T.dominos
    have vertical_implies_not_horizontal : ∀ T : Tiling (Rectangle (n + 2) 2),
        Domino.vertical 1 1 ∈ T.dominos → Domino.horizontal 1 1 ∉ T.dominos := by
      intro T hv hh
      exact vertical_horizontal_disjoint T ⟨hv, hh⟩
    -- Helper: if vertical 1 1 ∉ T.dominos, then horizontal 1 1 ∈ T.dominos  
    have not_vertical_implies_horizontal : ∀ T : Tiling (Rectangle (n + 2) 2),
        Domino.vertical 1 1 ∉ T.dominos → Domino.horizontal 1 1 ∈ T.dominos := by
      intro T hnv
      rcases classification T with hv | hh
      · exact absurd hv hnv
      · exact hh
    -- Use classical logic for decidability
    have : ∀ T : Tiling (Rectangle (n + 2) 2), Decidable (Domino.vertical 1 1 ∈ T.dominos) := 
      fun T => Classical.dec _
    have : DecidableEq ℕ := Classical.decEq ℕ
    -- Define the forward map
    let toSum : Tiling (Rectangle (n + 2) 2) → Tiling (Rectangle n 2) ⊕ Tiling (Rectangle (n + 1) 2) := 
      fun T => if hv : Domino.vertical 1 1 ∈ T.dominos 
               then Sum.inr (restrictTilingRight (n + 2) T 1 (fault_at_1_if_vertical (n + 2) (by omega) T hv))
               else if hn : n = 0 
                    then Sum.inl (hn ▸ emptyTiling2)
                    else Sum.inl (by
                      have hh := not_vertical_implies_horizontal T hv
                      have hn3 : n + 2 ≥ 3 := by omega
                      have hfault := fault_at_2_if_horizontal (n + 2) hn3 T hh
                      have hrestrict := restrictTilingRight (n + 2) T 2 hfault
                      simp only [show n + 2 - 2 = n by omega] at hrestrict
                      exact hrestrict)
    -- Define the inverse map  
    let fromSum : Tiling (Rectangle n 2) ⊕ Tiling (Rectangle (n + 1) 2) → Tiling (Rectangle (n + 2) 2) :=
      fun s => match s with
               | Sum.inl T => prependHorizontalPair n T
               | Sum.inr T => prependVertical (n + 1) T
    -- Construct the equivalence
    refine ⟨toSum, fromSum, ?_, ?_⟩
    -- Proof that fromSum ∘ toSum = id (left inverse)
    · intro T
      simp only [toSum, fromSum]
      by_cases hv : Domino.vertical 1 1 ∈ T.dominos
      · -- Case: vertical 1 1 ∈ T.dominos
        simp only [hv, dite_true]
        -- Need to show: prependVertical (n+1) (restrictTilingRight (n+2) T 1 _) = T
        -- This requires showing the dominos are equal
        apply Tiling.ext
        -- Show: {vertical 1 1} ∪ (restrictTilingRight ...).dominos.image (shiftNat 1) = T.dominos
        simp only [prependVertical, restrictTilingRight]
        -- The key insight: T.dominos = {vertical 1 1} ∪ {d ∈ T.dominos | d.inRightPart 1}
        -- because at fault 1, the only domino in left part is vertical 1 1
        ext d
        simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_image, Set.mem_sep_iff]
        constructor
        · intro h
          rcases h with rfl | ⟨d'', ⟨d', ⟨hd'_mem, hd'_right⟩, hd'_eq⟩, hd''_eq⟩
          · exact hv
          · -- d = d''.shiftNat 1 and d'' = d'.shiftNeg 1 and d' ∈ T.dominos
            subst hd'_eq hd''_eq
            rw [Domino.shiftNat_shiftNeg]
            exact hd'_mem
        · intro hd
          have hfault := fault_at_1_if_vertical (n + 2) (by omega) T hv
          have hlr := domino_left_or_right_at_fault hfault d hd
          rcases hlr with hleft | hright
          · -- d is in left part, so d = vertical 1 1
            left
            cases d with
            | horizontal i j =>
              exfalso
              have hsub := domino_subset_rect (n + 2) T (Domino.horizontal i j) hd
              have hi_ge : i ≥ 1 := by
                have := hsub (Set.mem_insert (i, j) _)
                simp only [Rectangle, Set.mem_ofPred_eq] at this
                exact this.1
              have hi1_le : i + 1 ≤ 1 := hleft (i + 1, j) (by simp [Domino.toShape])
              omega
            | vertical i j =>
              have hsub := domino_subset_rect (n + 2) T (Domino.vertical i j) hd
              have h1 : (i, j) ∈ Rectangle (n + 2) 2 := hsub (by simp [Domino.toShape])
              have h2 : (i, j + 1) ∈ Rectangle (n + 2) 2 := hsub (by simp [Domino.toShape])
              have hi_ge : i ≥ 1 := by simp only [Rectangle, Set.mem_ofPred_eq] at h1; exact h1.1
              have hi_le : i ≤ 1 := hleft (i, j) (by simp [Domino.toShape])
              have hj_ge : j ≥ 1 := by simp only [Rectangle, Set.mem_ofPred_eq] at h1; exact h1.2.2.1
              have hj1_le : j + 1 ≤ 2 := by simp only [Rectangle, Set.mem_ofPred_eq] at h2; exact h2.2.2.2
              simp only [Domino.vertical.injEq]; omega
          · -- d is in right part
            right
            refine ⟨d.shiftNeg 1, ⟨d, ⟨hd, hright⟩, rfl⟩, Domino.shiftNat_shiftNeg d 1⟩
      · -- Case: vertical 1 1 ∉ T.dominos (so horizontal 1 1 ∈ T.dominos)
        simp only [hv, dite_false]
        by_cases hn : n = 0
        · -- n = 0: special case
          simp only [hn, dite_true]
          -- Need to show: prependHorizontalPair 0 emptyTiling2 = T
          -- When n = 0, Rectangle 2 2 is covered by exactly {horizontal 1 1, horizontal 1 2}
          subst hn
          apply Tiling.ext
          simp only [prependHorizontalPair]
          -- emptyTiling2.dominos = ∅
          have hempty_dominos : emptyTiling2.dominos = ∅ := by
            have hsub : emptyTiling2.dominos ⊆ ∅ := by
              intro d hd
              have hsub' : d.toShape ⊆ Rectangle 0 2 := by
                rw [← emptyTiling2.cover]
                exact Set.subset_biUnion_of_mem hd
              rw [Rectangle_zero_left] at hsub'
              cases d with
              | horizontal i j =>
                have := hsub' (Set.mem_insert (i, j) _)
                exact this
              | vertical i j =>
                have := hsub' (Set.mem_insert (i, j) _)
                exact this
            exact Set.subset_eq_empty hsub rfl
          rw [hempty_dominos, Set.image_empty, Set.union_empty]
          -- Need to show: {horizontal 1 1, horizontal 1 2} = T.dominos
          have hh := not_vertical_implies_horizontal T hv
          have hh2 := horizontal_12_if_horizontal_11 2 (by omega) T hh
          ext d
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          constructor
          · intro hd
            rcases hd with rfl | rfl
            · exact hh
            · exact hh2
          · intro hd
            -- Every domino in T is either horizontal 1 1 or horizontal 1 2
            cases d with
            | horizontal i j =>
              have hsub := domino_subset_rect 2 T (Domino.horizontal i j) hd
              have h1 : (i, j) ∈ Rectangle 2 2 := hsub (by simp [Domino.toShape])
              have h2 : (i + 1, j) ∈ Rectangle 2 2 := hsub (by simp [Domino.toShape])
              simp only [Rectangle, Set.mem_ofPred_eq] at h1 h2
              have hi : i = 1 := by omega
              have hj : j = 1 ∨ j = 2 := by omega
              rcases hj with rfl | rfl
              · left; simp only [hi]
              · right; simp only [hi]
            | vertical i j =>
              -- vertical dominos are impossible when horizontal 1 1 is present
              exfalso
              have hsub := domino_subset_rect 2 T (Domino.vertical i j) hd
              have h1 : (i, j) ∈ Rectangle 2 2 := hsub (by simp [Domino.toShape])
              have h2 : (i, j + 1) ∈ Rectangle 2 2 := hsub (by simp [Domino.toShape])
              simp only [Rectangle, Set.mem_ofPred_eq] at h1 h2
              have hi : i = 1 ∨ i = 2 := by omega
              have hj : j = 1 := by omega
              -- If i = 1, then vertical 1 1 ∈ T.dominos, contradicting hv
              -- If i = 2, then vertical 2 1 overlaps with horizontal 1 1 or horizontal 1 2
              rcases hi with rfl | rfl
              · -- i = 1: vertical 1 1 ∈ T.dominos
                have : Domino.vertical 1 1 ∈ T.dominos := by simp only [hj] at hd; exact hd
                exact hv this
              · -- i = 2: vertical 2 1 overlaps with horizontal 1 1 at (2, 1)
                have hdisj := T.pairwise_disjoint hh hd
                have hne : Domino.horizontal 1 1 ≠ Domino.vertical 2 j := by simp
                have : Disjoint (Domino.horizontal 1 1).toShape (Domino.vertical 2 j).toShape := hdisj hne
                have h21_h : ((2 : ℤ), (1 : ℤ)) ∈ (Domino.horizontal 1 1).toShape := by simp [Domino.toShape]
                have h21_v : ((2 : ℤ), (1 : ℤ)) ∈ (Domino.vertical 2 j).toShape := by simp [Domino.toShape, hj]
                exact Set.disjoint_iff.mp this ⟨h21_h, h21_v⟩
        · -- n ≥ 1: use restrictTilingRight
          simp only [hn, dite_false]
          -- Need to show: prependHorizontalPair n (restrictTilingRight (n+2) T 2 _) = T
          apply Tiling.ext
          simp only [prependHorizontalPair, restrictTilingRight]
          -- Similar to the vertical case: T.dominos = {h 1 1, h 1 2} ∪ {d ∈ T.dominos | d.inRightPart 2}
          ext d
          simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image]
          constructor
          · intro h
            rcases h with (rfl | rfl) | ⟨d'', ⟨d', ⟨hd'_mem, hd'_right⟩, hd'_eq⟩, hd''_eq⟩
            · exact not_vertical_implies_horizontal T hv
            · exact horizontal_12_if_horizontal_11 (n + 2) (by omega) T (not_vertical_implies_horizontal T hv)
            · subst hd'_eq hd''_eq; rw [Domino.shiftNat_shiftNeg]; exact hd'_mem
          · intro hd
            have hh := not_vertical_implies_horizontal T hv
            have hn3 : n + 2 ≥ 3 := by omega
            have hfault := fault_at_2_if_horizontal (n + 2) hn3 T hh
            have hlr := domino_left_or_right_at_fault hfault d hd
            rcases hlr with hleft | hright
            · -- d is in left part at fault 2, so d = horizontal 1 1 or horizontal 1 2
              cases d with
              | horizontal i j =>
                have hsub := domino_subset_rect (n + 2) T (Domino.horizontal i j) hd
                have h1 : (i, j) ∈ Rectangle (n + 2) 2 := hsub (by simp [Domino.toShape])
                have h2 : (i + 1, j) ∈ Rectangle (n + 2) 2 := hsub (by simp [Domino.toShape])
                simp only [Rectangle, Set.mem_ofPred_eq] at h1 h2
                have hi1_le : i + 1 ≤ 2 := hleft (i + 1, j) (by simp [Domino.toShape])
                have hi_ge : i ≥ 1 := h1.1
                have hj12 : j = 1 ∨ j = 2 := by omega
                have hi_eq : i = 1 := by omega
                rcases hj12 with rfl | rfl
                · left; left; simp only [hi_eq]
                · left; right; simp only [hi_eq]
              | vertical i j =>
                exfalso
                have hsub := domino_subset_rect (n + 2) T (Domino.vertical i j) hd
                have h1 : (i, j) ∈ Rectangle (n + 2) 2 := hsub (by simp [Domino.toShape])
                simp only [Rectangle, Set.mem_ofPred_eq] at h1
                have hi_ge : i ≥ 1 := h1.1
                have hi_le : i ≤ 2 := hleft (i, j) (by simp [Domino.toShape])
                have hj_ge : j ≥ 1 := h1.2.2.1
                -- vertical i j with 1 ≤ i ≤ 2 and j ≥ 1 means i ∈ {1, 2}
                -- If i = 1: vertical 1 1 ∈ T.dominos, contradicting hv
                -- If i = 2: vertical 2 j overlaps with horizontal 1 j at (2, j)
                rcases (show i = 1 ∨ i = 2 by omega) with hi_eq | hi_eq
                · have hj1 : j = 1 := by
                    have h2' : (i, j + 1) ∈ Rectangle (n + 2) 2 := hsub (by simp [Domino.toShape])
                    simp only [Rectangle, Set.mem_ofPred_eq] at h2'
                    omega
                  have hv11 : Domino.vertical 1 1 ∈ T.dominos := by
                    simp only [hi_eq, hj1] at hd; exact hd
                  exact hv hv11
                · have hj12 : j = 1 := by
                    have h2' : (i, j + 1) ∈ Rectangle (n + 2) 2 := hsub (by simp [Domino.toShape])
                    simp only [Rectangle, Set.mem_ofPred_eq] at h2'
                    omega
                  have hh2 := horizontal_12_if_horizontal_11 (n + 2) (by omega) T hh
                  have hdisj := T.pairwise_disjoint hh hd
                  have hne : Domino.horizontal 1 1 ≠ Domino.vertical i j := by simp [hi_eq]
                  have hdisj' : Disjoint (Domino.horizontal 1 1).toShape (Domino.vertical i j).toShape := hdisj hne
                  have h21_h : ((2 : ℤ), (1 : ℤ)) ∈ (Domino.horizontal 1 1).toShape := by simp [Domino.toShape]
                  have h21_v : ((2 : ℤ), (1 : ℤ)) ∈ (Domino.vertical i j).toShape := by simp [Domino.toShape, hi_eq, hj12]
                  exact Set.disjoint_iff.mp hdisj' ⟨h21_h, h21_v⟩
            · -- d is in right part
              right
              refine ⟨d.shiftNeg 2, ⟨d, ⟨hd, hright⟩, rfl⟩, Domino.shiftNat_shiftNeg d 2⟩
    -- Proof that toSum ∘ fromSum = id (right inverse)
    · intro s
      simp only [toSum, fromSum]
      rcases s with T | T
      · -- Case: Sum.inl T (from Rectangle n 2)
        -- Need to show: toSum (prependHorizontalPair n T) = Sum.inl T
        -- First, show vertical 1 1 ∉ (prependHorizontalPair n T).dominos
        have hv_not : Domino.vertical 1 1 ∉ (prependHorizontalPair n T).dominos := by
          simp only [prependHorizontalPair, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          constructor
          · constructor
            · exact fun h => Domino.noConfusion h
            · exact fun h => Domino.noConfusion h
          · exact vertical_11_not_in_shiftNat2_image n T
        simp only [hv_not, dite_false]
        by_cases hn : n = 0
        · simp only [hn, dite_true]
          -- Need to show: Sum.inl (0 ▸ emptyTiling2) = Sum.inl T
          -- When n = 0, T : Tiling (Rectangle 0 2) must be emptyTiling2
          subst hn
          congr 1
          apply Tiling.ext
          -- Rectangle 0 2 = ∅, so both tilings have empty dominos
          have hT_empty : T.dominos = ∅ := by
            have hsub : T.dominos ⊆ ∅ := by
              intro d hd
              have hsub' : d.toShape ⊆ Rectangle 0 2 := by
                rw [← T.cover]
                exact Set.subset_biUnion_of_mem hd
              rw [Rectangle_zero_left] at hsub'
              cases d with
              | horizontal i j => exact hsub' (Set.mem_insert (i, j) _)
              | vertical i j => exact hsub' (Set.mem_insert (i, j) _)
            exact Set.subset_eq_empty hsub rfl
          have hempty : emptyTiling2.dominos = ∅ := by
            have hsub : emptyTiling2.dominos ⊆ ∅ := by
              intro d hd
              have hsub' : d.toShape ⊆ Rectangle 0 2 := by
                rw [← emptyTiling2.cover]
                exact Set.subset_biUnion_of_mem hd
              rw [Rectangle_zero_left] at hsub'
              cases d with
              | horizontal i j => exact hsub' (Set.mem_insert (i, j) _)
              | vertical i j => exact hsub' (Set.mem_insert (i, j) _)
            exact Set.subset_eq_empty hsub rfl
          rw [hT_empty, hempty]
        · simp only [hn, dite_false]
          -- Need to show: Sum.inl (restrictTilingRight ...) = Sum.inl T
          -- This means restrictTilingRight (prependHorizontalPair n T) = T
          congr 1
          apply Tiling.ext
          simp only [restrictTilingRight, prependHorizontalPair]
          -- Similar to the vertical case
          ext d
          simp only [Set.mem_image, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
          constructor
          · intro ⟨d', ⟨hd'_mem, hd'_right⟩, hd_eq⟩
            cases hd'_mem with
            | inl heq =>
              rcases heq with rfl | rfl
              · -- d' = horizontal 1 1, which is in left part at fault 2
                exfalso
                have h : (2 : ℤ) ≥ 2 + 1 := hd'_right (2, 1) (by simp [Domino.toShape])
                omega
              · -- d' = horizontal 1 2, which is in left part at fault 2
                exfalso
                have h : (2 : ℤ) ≥ 2 + 1 := hd'_right (2, 2) (by simp [Domino.toShape])
                omega
            | inr hex =>
              obtain ⟨d'', hd''_mem, hd''_eq⟩ := hex
              subst hd''_eq hd_eq
              simp only [Domino.shiftNeg_shiftNat]
              exact hd''_mem
          · intro hd
            use d.shiftNat 2
            constructor
            · constructor
              · right; exact ⟨d, hd, rfl⟩
              · simp only [Domino.inRightPart, Domino.shiftNat_toShape]
                intro p hp
                simp only [Set.mem_image] at hp
                obtain ⟨⟨x, y⟩, hxy, rfl, rfl⟩ := hp
                have hsub := domino_subset_rect n T d hd
                cases d with
                | horizontal i j =>
                  have h1 : (i, j) ∈ Rectangle n 2 := hsub (by simp [Domino.toShape])
                  simp only [Rectangle, Set.mem_ofPred_eq] at h1
                  simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff] at hxy
                  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
                | vertical i j =>
                  have h1 : (i, j) ∈ Rectangle n 2 := hsub (by simp [Domino.toShape])
                  simp only [Rectangle, Set.mem_ofPred_eq] at h1
                  simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff] at hxy
                  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
            · exact Domino.shiftNeg_shiftNat d 2
      · -- Case: Sum.inr T (from Rectangle (n+1) 2)
        -- Need to show: toSum (prependVertical (n+1) T) = Sum.inr T
        -- First, show vertical 1 1 ∈ (prependVertical (n+1) T).dominos
        have hv : Domino.vertical 1 1 ∈ (prependVertical (n + 1) T).dominos := by
          simp only [prependVertical, Set.mem_union, Set.mem_singleton_iff, true_or]
        simp only [hv, dite_true]
        -- Need to show: Sum.inr (restrictTilingRight ...) = Sum.inr T
        -- This means restrictTilingRight (prependVertical (n+1) T) = T
        congr 1
        apply Tiling.ext
        simp only [restrictTilingRight, prependVertical]
        -- The right part of prependVertical T at fault 1 is exactly T.dominos.image (shiftNat 1)
        -- And restricting shifts back by 1, so we get T.dominos
        ext d
        simp only [Set.mem_image, Set.mem_union, Set.mem_singleton_iff]
        constructor
        · intro ⟨d', ⟨hd'_mem, hd'_right⟩, hd_eq⟩
          cases hd'_mem with
          | inl heq =>
            -- d' = vertical 1 1, which is in left part, not right part
            exfalso
            subst heq
            have h : (1 : ℤ) ≥ 1 + 1 := hd'_right (1, 1) (by simp [Domino.toShape])
            omega
          | inr hex =>
            -- d' is in the shifted part
            obtain ⟨d'', hd''_mem, hd''_eq⟩ := hex
            subst hd''_eq hd_eq
            simp only [Domino.shiftNeg_shiftNat]
            exact hd''_mem
        · intro hd
          use d.shiftNat 1
          constructor
          · constructor
            · right; exact ⟨d, hd, rfl⟩
            · simp only [Domino.inRightPart, Domino.shiftNat_toShape]
              intro p hp
              simp only [Set.mem_image] at hp
              obtain ⟨⟨x, y⟩, hxy, rfl, rfl⟩ := hp
              have hsub := domino_subset_rect (n + 1) T d hd
              cases d with
              | horizontal i j =>
                have h1 : (i, j) ∈ Rectangle (n + 1) 2 := hsub (by simp [Domino.toShape])
                simp only [Rectangle, Set.mem_ofPred_eq] at h1
                simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff] at hxy
                rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
              | vertical i j =>
                have h1 : (i, j) ∈ Rectangle (n + 1) 2 := hsub (by simp [Domino.toShape])
                simp only [Rectangle, Set.mem_ofPred_eq] at h1
                simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff] at hxy
                rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
          · exact Domino.shiftNeg_shiftNat d 1
  -- Provide Finite instances by extracting from tilingsHeight2_isFiniteType
  -- tilingsHeight2_isFiniteType k says {a : Σ n, Tiling (Rectangle n 2) | weight a = k} is finite
  -- This implies Tiling (Rectangle k 2) is finite
  have hfin_n : Set.Finite (Set.univ : Set (Tiling (Rectangle n 2))) := by
    have h := tilingsHeight2_isFiniteType n
    let f : Tiling (Rectangle n 2) → Σ m : ℕ, Tiling (Rectangle m 2) := fun T => ⟨n, T⟩
    have hf : Function.Injective f := by
      intro T1 T2 heq
      simp only [f, Sigma.mk.injEq] at heq
      exact eq_of_heq heq.2
    have hrange : Set.range f ⊆ {a : Σ m : ℕ, Tiling (Rectangle m 2) | TilingsHeight2.weight a = n} := by
      intro x hx
      simp only [Set.mem_range, f] at hx
      obtain ⟨T, rfl⟩ := hx
      simp only [TilingsHeight2, Set.mem_ofPred_eq]
    have hrange_fin : Set.Finite (Set.range f) := h.subset hrange
    convert hrange_fin.preimage hf.injOn
    ext T
    simp only [Set.mem_univ, Set.mem_preimage, Set.mem_range, true_iff]
    exact ⟨T, rfl⟩
  have hfin_n1 : Set.Finite (Set.univ : Set (Tiling (Rectangle (n + 1) 2))) := by
    have h := tilingsHeight2_isFiniteType (n + 1)
    let f : Tiling (Rectangle (n + 1) 2) → Σ m : ℕ, Tiling (Rectangle m 2) := fun T => ⟨n + 1, T⟩
    have hf : Function.Injective f := by
      intro T1 T2 heq
      simp only [f, Sigma.mk.injEq] at heq
      exact eq_of_heq heq.2
    have hrange : Set.range f ⊆ {a : Σ m : ℕ, Tiling (Rectangle m 2) | TilingsHeight2.weight a = n + 1} := by
      intro x hx
      simp only [Set.mem_range, f] at hx
      obtain ⟨T, rfl⟩ := hx
      simp only [TilingsHeight2, Set.mem_ofPred_eq]
    have hrange_fin : Set.Finite (Set.range f) := h.subset hrange
    convert hrange_fin.preimage hf.injOn
    ext T
    simp only [Set.mem_univ, Set.mem_preimage, Set.mem_range, true_iff]
    exact ⟨T, rfl⟩
  have : Finite (Tiling (Rectangle n 2)) := Set.finite_univ_iff.mp hfin_n
  have : Finite (Tiling (Rectangle (n + 1) 2)) := Set.finite_univ_iff.mp hfin_n1
  rw [Nat.card_congr e, Nat.card_sum, add_comm]

/-- The number of domino tilings of a 2×n rectangle equals the (n+1)-th Fibonacci number -/
lemma numTilings_2_n (n : ℕ) : d_[n, 2] = Nat.fib (n + 1) := by
  -- The proof uses strong induction with the Fibonacci recurrence.
  -- Base cases: d_[0, 2] = 1 = fib(1), d_[1, 2] = 1 = fib(2)
  -- Inductive step: d_[n+2, 2] = d_[n, 2] + d_[n+1, 2] by numTilings_recurrence
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · -- n = 0
      rw [numTilings_0_2]
      rfl
    · -- n = 1
      rw [numTilings_1_2]
      rfl
    · -- n + 2: use the Fibonacci recurrence
      -- By IH: d_[n, 2] = Nat.fib (n + 1) and d_[n+1, 2] = Nat.fib (n + 2)
      have h1 := ih n (by omega)
      have h2 := ih (n + 1) (by omega)
      simp only [show n + 2 + 1 = n + 3 by ring]
      simp only [show n + 1 + 1 = n + 2 by ring] at h2
      -- By Fibonacci recurrence: Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2)
      have hfib := @Nat.fib_add_two (n + 1)
      simp only [show n + 1 + 1 = n + 2 by ring, show n + 1 + 2 = n + 3 by ring] at hfib
      rw [hfib, ← h1, ← h2]
      -- Apply the recurrence lemma
      exact numTilings_recurrence n

/-- The count of tilings at weight n equals the number of tilings of R_{n,2} -/
lemma countOfWeight_tilingsHeight2_eq (n : ℕ) :
    TilingsHeight2.countOfWeight tilingsHeight2_isFiniteType n = d_[n, 2] := by
  -- This follows from the definition: elements of weight n are exactly tilings of R_{n,2}
  unfold WeightedSet.countOfWeight numTilings
  -- Show the set of elements of weight n is in bijection with tilings of Rectangle n 2
  have h_eq : {a : Σ m : ℕ, Tiling (Rectangle m 2) | TilingsHeight2.weight a = n} =
              Set.range (fun T : Tiling (Rectangle n 2) => (⟨n, T⟩ : Σ m : ℕ, Tiling (Rectangle m 2))) := by
    ext ⟨m, T⟩
    simp only [TilingsHeight2, Set.mem_ofPred_eq, Set.mem_range, Sigma.mk.injEq]
    constructor
    · intro hm
      use hm.symm ▸ T
      exact ⟨hm.symm, by simp⟩
    · intro ⟨T', hm, hT⟩
      exact hm.symm
  have h_finite := tilingsHeight2_isFiniteType n
  have h_card : h_finite.toFinset.card = {a : Σ m : ℕ, Tiling (Rectangle m 2) | TilingsHeight2.weight a = n}.ncard := by
    rw [Set.ncard]
    simp only [h_finite.encard_eq_coe_toFinset_card, ENat.toNat_natCast]
  rw [h_card, h_eq]
  have h_inj : Function.Injective (fun T : Tiling (Rectangle n 2) => (⟨n, T⟩ : Σ m : ℕ, Tiling (Rectangle m 2))) := by
    intro T1 T2 heq
    exact Sigma.mk.inj heq |>.2 |> eq_of_heq
  rw [Set.ncard_range_of_injective h_inj]

/-- The generating function of height-2 tilings equals 1/(1-x-x²),
    which is the Fibonacci generating function -/
lemma weightGenFun_tilingsHeight2 :
    TilingsHeight2.weightGenFun (R := ℚ) tilingsHeight2_isFiniteType =
      PowerSeries.mk fun n => (Nat.fib (n + 1) : ℚ) := by
  -- The n-th coefficient of the LHS is countOfWeight n
  -- which equals numTilings n 2 by countOfWeight_tilingsHeight2_eq
  -- which equals Nat.fib (n + 1) by numTilings_2_n
  ext n
  simp only [WeightedSet.weightGenFun, PowerSeries.coeff_mk]
  rw [countOfWeight_tilingsHeight2_eq, numTilings_2_n]

/-- The set of dominos in a rectangle is finite -/
lemma dominosInRectangle_finite (n m : ℕ) : Set.Finite (DominosInRectangle n m) := by
  have h : DominosInRectangle n m ⊆
      (Set.Icc (1 : ℤ) n ×ˢ Set.Icc (1 : ℤ) m).image (fun p => Domino.horizontal p.1 p.2) ∪
      (Set.Icc (1 : ℤ) n ×ˢ Set.Icc (1 : ℤ) m).image (fun p => Domino.vertical p.1 p.2) := by
    intro d hd
    cases d with
    | horizontal i j =>
      left
      simp only [Set.mem_image, Set.mem_prod, Set.mem_Icc]
      use (i, j)
      simp only [DominosInRectangle, Domino.toShape, Set.subset_def, Set.mem_ofPred_eq] at hd
      have h1 := hd (i, j) (by simp)
      simp only [Rectangle, Set.mem_ofPred_eq] at h1
      refine ⟨⟨⟨h1.1, ?_⟩, ⟨h1.2.2.1, h1.2.2.2⟩⟩, rfl⟩
      omega
    | vertical i j =>
      right
      simp only [Set.mem_image, Set.mem_prod, Set.mem_Icc]
      use (i, j)
      simp only [DominosInRectangle, Domino.toShape, Set.subset_def, Set.mem_ofPred_eq] at hd
      have h1 := hd (i, j) (by simp)
      simp only [Rectangle, Set.mem_ofPred_eq] at h1
      refine ⟨⟨⟨h1.1, h1.2.1⟩, ⟨h1.2.2.1, ?_⟩⟩, rfl⟩
      omega
  apply Set.Finite.subset _ h
  apply Set.Finite.union
  · apply Set.Finite.image
    apply Set.Finite.prod
    · exact Set.finite_Icc (1 : ℤ) n
    · exact Set.finite_Icc (1 : ℤ) m
  · apply Set.Finite.image
    apply Set.Finite.prod
    · exact Set.finite_Icc (1 : ℤ) n
    · exact Set.finite_Icc (1 : ℤ) m

/-- A tiling's dominos are contained in DominosInRectangle -/
lemma tiling_dominos_subset (n m : ℕ) (T : Tiling (Rectangle n m)) :
    T.dominos ⊆ DominosInRectangle n m := by
  intro d hd
  simp only [DominosInRectangle, Set.mem_ofPred_eq]
  have h : d.toShape ⊆ ⋃ d' ∈ T.dominos, d'.toShape := by
    intro p hp
    simp only [Set.mem_iUnion]
    exact ⟨d, hd, hp⟩
  rw [T.cover] at h
  exact h

/-- The set of tilings of a rectangle is finite -/
lemma tilings_finite (n m : ℕ) : Set.Finite (Set.univ : Set (Tiling (Rectangle n m))) := by
  let f : Tiling (Rectangle n m) → Set Domino := fun T => T.dominos
  have hf : Function.Injective f := by
    intro T₁ T₂ h
    cases T₁; cases T₂
    simp only [f] at h
    congr
  have h_range : Set.range f ⊆ 𝒫 (DominosInRectangle n m) := by
    intro s hs
    simp only [Set.mem_range, f] at hs
    obtain ⟨T, rfl⟩ := hs
    simp only [Set.mem_powerset_iff]
    exact tiling_dominos_subset n m T
  have h_powerset_finite : Set.Finite (𝒫 (DominosInRectangle n m)) := by
    exact (dominosInRectangle_finite n m).powerset
  have h_range_finite : Set.Finite (Set.range f) := by
    exact h_powerset_finite.subset h_range
  have h_univ_finite : Set.Finite (f ⁻¹' Set.range f) := by
    apply h_range_finite.preimage
    exact hf.injOn
  convert h_univ_finite
  ext x
  simp only [Set.mem_univ, Set.mem_preimage, Set.mem_range, exists_apply_eq_apply]

end DominoTilingsZ
end


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
private lemma pv_mem_rectangle_iff
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

/--
[WeightedSets](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma x_disjointUnion_weight_inl
-- given
  (W₁ : WeightedSet α)
  (W₂ : WeightedSet β)
  (a : α) :
-- imply
  (WeightedSet.disjointUnion W₁ W₂).weight (Sum.inl a) = W₁.weight a := by
-- proof
  apply WeightedSet.disjointUnion_weight_inl W₁ W₂ a

/--
[WeightedSets](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma x_disjointUnion_weight_inr
-- given
  (W₁ : WeightedSet α)
  (W₂ : WeightedSet β)
  (b : β) :
-- imply
  (WeightedSet.disjointUnion W₁ W₂).weight (Sum.inr b) = W₂.weight b := by
-- proof
  apply WeightedSet.disjointUnion_weight_inr W₁ W₂ b

/--
[WeightedSets](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma x_prod_weight
-- given
  (W₁ : WeightedSet α)
  (W₂ : WeightedSet β)
  (p : α × β) :
-- imply
  (WeightedSet.prod W₁ W₂).weight p = W₁.weight p.1 + W₂.weight p.2 := by
-- proof
  apply WeightedSet.prod_weight W₁ W₂ p

/--
[WeightedSets](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma x_numTilings_0_2 :
-- imply
  numTilings 0 2 = 1 := by
-- proof
  apply DominoTilingsZ.numTilings_0_2

/--
[WeightedSets](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma x_numTilings_1_2 :
-- imply
  numTilings 1 2 = 1 := by
-- proof
  apply DominoTilingsZ.numTilings_1_2

/--
[weight_gen_fun_eq_sum_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma pv_binaryStrings_countOfWeight
-- given
  (n : ℕ) :
-- imply
  BinaryStrings.countOfWeight binaryStrings_isFiniteType n = 2 ^ n := by
-- proof
  apply WeightedSetExamples.binaryStrings_countOfWeight n

/--
[weight_gen_fun_eq_sum_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma pv_countOfWeight_zero :
-- imply
  PositiveIntegers.countOfWeight positiveIntegers_isFiniteType 0 = 0 := by
-- proof
  apply WeightedSetExamples.countOfWeight_zero

/--
[weight_gen_fun_eq_sum_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma pv_countOfWeight_pos
-- given
  (n : ℕ)
  (hn : 0 < n) :
-- imply
  PositiveIntegers.countOfWeight positiveIntegers_isFiniteType n = 1 := by
-- proof
  apply WeightedSetExamples.countOfWeight_pos n hn

/--
[weight_gen_fun_eq_sum_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma pv_domino_subset_rect
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (d : Domino)
  (hd : d ∈ T.dominos) :
-- imply
  d.toShape ⊆ Rectangle n 2 := by
-- proof
  apply DominoTilingsZ.domino_subset_rect n T d hd

/--
[weight_gen_fun_eq_sum_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma pv_cell_11_in_rect
-- given
  (n : ℕ)
  (hn : n ≥ 1) :
-- imply
  (1, 1) ∈ Rectangle n 2 := by
-- proof
  apply DominoTilingsZ.cell_11_in_rect n hn

/--
[weight_gen_fun_eq_sum_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma pv_no_horizontal_at_1_if_vertical
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (i j : ℤ)
  (hv : Domino.vertical 1 1 ∈ T.dominos)
  (hd : Domino.horizontal i j ∈ T.dominos) :
-- imply
  i < 1 ∨ i ≥ 2 := by
-- proof
  apply DominoTilingsZ.no_horizontal_at_1_if_vertical n T hv i j hd

/--
[weight_gen_fun_eq_sum_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma pv_cell_12_in_rect
-- given
  (n : ℕ)
  (hn : n ≥ 1) :
-- imply
  (1, 2) ∈ Rectangle n 2 := by
-- proof
  apply DominoTilingsZ.cell_12_in_rect n hn

/--
[weight_gen_fun_eq_sum_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma pv_exists_domino_covering_12
-- given
  (n : ℕ)
  (hn : n ≥ 1)
  (T : Tiling (Rectangle n 2)) :
-- imply
  ∃ d ∈ T.dominos, (1, 2) ∈ d.toShape := by
-- proof
  apply DominoTilingsZ.exists_domino_covering_12 n hn T

/--
[weight_gen_fun_eq_sum_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma pv_domino_covering_12_valid
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (d : Domino)
  (hd : d ∈ T.dominos)
  (h : (1, 2) ∈ d.toShape) :
-- imply
  d = .vertical 1 1 ∨ d = .horizontal 1 2 := by
-- proof
  apply DominoTilingsZ.domino_covering_12_valid n T d hd h

/--
[weight_gen_fun_eq_sum_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma pv_no_horizontal_at_2_if_horizontal_pair
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (i j : ℤ)
  (hh1 : Domino.horizontal 1 1 ∈ T.dominos)
  (hh2 : Domino.horizontal 1 2 ∈ T.dominos)
  (hd : Domino.horizontal i j ∈ T.dominos) :
-- imply
  i < 2 ∨ i ≥ 3 := by
-- proof
  apply DominoTilingsZ.no_horizontal_at_2_if_horizontal_pair n T hh1 hh2 i j hd

/--
[weight_gen_fun_eq_sum_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma pv_faultfree_width2_has_horizontal_at_1
-- given
  (T : Tiling (Rectangle 2 2))
  (hff : isFaultfree 2 T) :
-- imply
  Domino.horizontal 1 1 ∈ T.dominos ∨ Domino.horizontal 1 2 ∈ T.dominos := by
-- proof
  apply DominoTilingsZ.faultfree_width2_has_horizontal_at_1 T hff

/--
[weight_gen_fun_eq_sum_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma pv_exists_domino_covering'
-- given
  (n : ℕ)
  (i j : ℤ)
  (h : (i, j) ∈ Rectangle n 2)
  (T : Tiling (Rectangle n 2)) :
-- imply
  ∃ d ∈ T.dominos, (i, j) ∈ d.toShape := by
-- proof
  apply DominoTilingsZ.exists_domino_covering' n T i j h

/--
[weight_gen_fun_eq_sum_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma pv_horizontal_11_implies_12'
-- given
  (T : Tiling (Rectangle 2 2))
  (hh : Domino.horizontal 1 1 ∈ T.dominos) :
-- imply
  Domino.horizontal 1 2 ∈ T.dominos := by
-- proof
  apply DominoTilingsZ.horizontal_11_implies_12' T hh

/--
[weight_gen_fun_eq_sum_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma pv_horizontal_12_implies_11'
-- given
  (T : Tiling (Rectangle 2 2))
  (hh : Domino.horizontal 1 2 ∈ T.dominos) :
-- imply
  Domino.horizontal 1 1 ∈ T.dominos := by
-- proof
  apply DominoTilingsZ.horizontal_12_implies_11' T hh

/--
[weight_gen_fun_eq_sum_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma pv_faultfree_width2_dominos
-- given
  (T : Tiling (Rectangle 2 2))
  (hff : isFaultfree 2 T) :
-- imply
  Domino.horizontal 1 1 ∈ T.dominos ∧ Domino.horizontal 1 2 ∈ T.dominos := by
-- proof
  apply DominoTilingsZ.faultfree_width2_dominos T hff

/--
[weight_gen_fun_eq_sum_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma pv_faultfree_width2_dominos_eq
-- given
  (T : Tiling (Rectangle 2 2))
  (hff : isFaultfree 2 T) :
-- imply
  T.dominos = {Domino.horizontal 1 1, Domino.horizontal 1 2} := by
-- proof
  apply DominoTilingsZ.faultfree_width2_dominos_eq T hff

/--
[weight_gen_fun_eq_sum_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma pv_shifted_domino_x_in_range'
  {n : ℕ}
  {T : Tiling (Rectangle n 2)}
  {d : Domino}
-- given
  (offset : ℕ)
  (p : ℤ × ℤ)
  (hd : d ∈ T.dominos)
  (hp : p ∈ (d.shiftNat offset).toShape) :
-- imply
  1 + (offset : ℤ) ≤ p.1 ∧ p.1 ≤ n + (offset : ℤ) := by
-- proof
  apply DominoTilingsZ.shifted_domino_x_in_range' hd offset p hp

/--
[weight_gen_fun_eq_sum_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma pv_find_component_index
-- given
  (k : ℕ)
  (widths : Fin k → ℕ)
  (x : ℕ)
  (hx : x < ∑ i, widths i) :
-- imply
  ∃ i : Fin k, (∑ j : Fin i.val, widths ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) ≤ x ∧ x < (∑ j : Fin i.val, widths ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) + widths i := by
-- proof
  apply DominoTilingsZ.find_component_index k widths x hx

/--
[weight_gen_fun_eq_sum_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma pv_partialWidthSum_add_le
-- given
  (k : ℕ)
  (i1 i2 : Fin k)
  (h : i1 < i2)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun T' : Tiling (Rectangle m 2) => isFaultfree m T'))) :
-- imply
  partialWidthSum k ts i1 + (ts i1).1 ≤ partialWidthSum k ts i2 := by
-- proof
  apply DominoTilingsZ.partialWidthSum_add_le k ts i1 i2 h

/--
[weight_gen_fun_eq_sum_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma pv_partialWidthSum_succ
-- given
  (k : ℕ)
  (i : Fin k)
  (hi : i.val + 1 < k)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun T' : Tiling (Rectangle m 2) => isFaultfree m T'))) :
-- imply
  partialWidthSum k ts ⟨i.val + 1, hi⟩ = partialWidthSum k ts i + (ts i).1 := by
-- proof
  apply DominoTilingsZ.partialWidthSum_succ k ts i hi

/--
[weight_gen_fun_eq_sum_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma pv_point_in_some_component
-- given
  (k : ℕ)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun T' : Tiling (Rectangle m 2) => isFaultfree m T')))
  (p : ℤ × ℤ)
  (hk : k ≥ 1)
  (hp : p ∈ Rectangle (∑ i : Fin k, (ts i).1) 2) :
-- imply
  ∃ i : Fin k, (partialWidthSum k ts i : ℤ) < p.1 ∧ p.1 ≤ partialWidthSum k ts i + (ts i).1 := by
-- proof
  apply DominoTilingsZ.point_in_some_component k hk ts p hp

/--
[weight_gen_fun_eq_sum_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma pv_sigma_fin_fun_ext
-- given
  (n m : ℕ)
  (f : Fin n → α)
  (g : Fin m → α)
  (h : n = m)
  (hfg : ∀ i : Fin m, f ⟨i.val, by omega⟩ = g i) :
-- imply
  (⟨n, f⟩ : Σ k, Fin k → α) = ⟨m, g⟩ := by
-- proof
  apply DominoTilingsZ.sigma_fin_fun_ext n m h f g hfg


-- created on 2026-10-20
-- updated on 2026-10-23
