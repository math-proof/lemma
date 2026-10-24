import Mathlib
import sympy.Basic
import sympy.series.formal.InfiniteProducts2
open PowerSeries
open scoped PowerSeries PowerSeries.WithPiTopology


section
-- ac-theorems


open scoped Polynomial
open Finset PowerSeries

noncomputable section

variable {K : Type*} [CommRing K]

namespace EssentiallyFinite

variable {I M : Type*} [Zero M]


/-- An essentially finite function has finite support. -/
lemma finite_support {f : I → M} (hf : EssentiallyFinite f) : (Function.support f).Finite :=
  hf
/-- A function with finite domain is essentially finite. -/
lemma of_finite [Finite I] (f : I → M) : EssentiallyFinite f :=
  Set.toFinite _

/-- A function indexed by a Fintype is essentially finite. -/
lemma of_fintype [Fintype I] (f : I → M) : EssentiallyFinite f :=
  Set.toFinite _

/-- A subfamily of an essentially finite family is essentially finite. -/
lemma subfamily {f : I → M} (J : Set I) (hf : EssentiallyFinite f) :
    EssentiallyFinite (fun i : J => f i) := by
  have h : {i : J | f i ≠ 0} ⊆ Subtype.val ⁻¹' {i | f i ≠ 0} := fun _ hx => hx
  exact Set.Finite.subset (hf.preimage Subtype.val_injective.injOn) h

/-- The constant function with value zero is essentially finite. -/
lemma const_zero : EssentiallyFinite (fun _ : I => (0 : M)) := zero


/-- `EssentiallyFinite f` is equivalent to `f i = 0` holding eventually in the cofinite filter.
    This is the key connection to the formulation used in the main theorems. -/
lemma iff_eventually_cofinite {f : I → M} :
    EssentiallyFinite f ↔ ∀ᶠ i in Filter.cofinite, f i = 0 := by
  rw [EssentiallyFinite, Filter.eventually_cofinite]
  simp only [Function.support, ne_eq]

/-- Alternative characterization: the set of nonzero values is finite. -/
lemma iff_finite_setOf_ne_zero {f : I → M} :
    EssentiallyFinite f ↔ {i | f i ≠ 0}.Finite := Iff.rfl

/-- Alternative characterization: the support is finite. -/
lemma iff_support_finite {f : I → M} :
    EssentiallyFinite f ↔ (Function.support f).Finite := Iff.rfl


section AddGroup
variable {M : Type*} [AddGroup M]


/-- The sum of two essentially finite families is essentially finite. -/
lemma add {f g : I → M} (hf : EssentiallyFinite f) (hg : EssentiallyFinite g) :
    EssentiallyFinite (f + g) := by
  apply Set.Finite.subset (hf.union hg)
  intro i hi
  simp only [Pi.add_apply, ne_eq, Function.mem_support] at hi
  by_contra h
  simp only [Set.mem_union, ne_eq, not_or, not_not, Function.mem_support] at h
  simp [h.1, h.2] at hi
/-- The negation of an essentially finite family is essentially finite. -/
lemma neg {f : I → M} (hf : EssentiallyFinite f) : EssentiallyFinite (-f) := by
  unfold EssentiallyFinite at *
  convert hf using 1
  ext i
  simp [Function.mem_support]

/-- The difference of two essentially finite families is essentially finite. -/
lemma sub {f g : I → M} (hf : EssentiallyFinite f) (hg : EssentiallyFinite g) :
    EssentiallyFinite (f - g) := by
  rw [sub_eq_add_neg]
  exact add hf (neg hg)

end AddGroup

section Ring
variable {R : Type*} [Ring R] [NoZeroDivisors R]

/-- Multiplication of an essentially finite family by a scalar is essentially finite. -/
lemma mul_const {f : I → R} (hf : EssentiallyFinite f) (c : R) :
    EssentiallyFinite (fun i => f i * c) := by
  apply Set.Finite.subset hf
  intro i hi
  simp only [ne_eq, Function.mem_support, mul_eq_zero, not_or] at hi
  exact hi.1

/-- Multiplication of a scalar by an essentially finite family is essentially finite. -/
lemma const_mul {f : I → R} (c : R) (hf : EssentiallyFinite f) :
    EssentiallyFinite (fun i => c * f i) := by
  apply Set.Finite.subset hf
  intro i hi
  simp only [ne_eq, Function.mem_support, mul_eq_zero, not_or] at hi
  exact hi.2

end Ring

lemma toFinsupp_apply {f : I → M} (hf : EssentiallyFinite f) (i : I) :
    hf.toFinsupp i = f i := rfl

lemma mem_supportFinset_iff {f : I → M} (hf : EssentiallyFinite f) (i : I) :
    i ∈ hf.supportFinset ↔ f i ≠ 0 := by
  simp only [supportFinset]
  exact Set.Finite.mem_toFinset hf

end EssentiallyFinite


namespace EssentiallyFiniteFamily

variable {I M : Type*} [Zero M]


@[simp] lemma zero_apply (i : I) : (0 : EssentiallyFiniteFamily I M) i = 0 := rfl

/-- The support of an essentially finite family is finite. -/
lemma finite_support (f : EssentiallyFiniteFamily I M) :
    (Function.support f.val).Finite := f.prop
/-- An essentially finite family satisfies the cofinite condition. -/
lemma eventually_eq_zero (f : EssentiallyFiniteFamily I M) :
    ∀ᶠ i in Filter.cofinite, f i = 0 :=
  EssentiallyFinite.iff_eventually_cofinite.mp f.prop

end EssentiallyFiniteFamily


section FiniteProductRules

variable {L : Type*} [CommSemiring L]

/-- **Finite Product Rule for Finite Sums** (Proposition prop.fps.prodrule-fin-fin)

A product of sums can be expanded into a sum over the Cartesian product:
`∏_{i=1}^n (∑_{k=1}^{m_i} p_{i,k}) = ∑_{(k₁,...,k_n) ∈ [m₁]×...×[m_n]} ∏_{i=1}^n p_{i,k_i}`

This is the generalized distributive law. -/
lemma prod_sum_eq_sum_prod_finset {n : ℕ} {m : Fin n → ℕ}
    (p : (i : Fin n) → Fin (m i) → L) :
    ∏ i : Fin n, ∑ k : Fin (m i), p i k =
    ∑ f : (i : Fin n) → Fin (m i), ∏ i : Fin n, p i (f i) :=
  Fintype.prod_sum p

/-- **Finite Product Rule for Finite Sums** (general index set version)

Same as above but with an arbitrary finite index set `N`. -/
lemma prod_sum_eq_sum_prod_finset' {N : Type*} [Fintype N] [DecidableEq N]
    {S : N → Type*} [∀ i, Fintype (S i)]
    (p : (i : N) → S i → L) :
    ∏ i : N, ∑ k : S i, p i k =
    ∑ f : (i : N) → S i, ∏ i : N, p i (f i) :=
  Fintype.prod_sum p

end FiniteProductRules


section FiniteProductInfiniteSums

open scoped PowerSeries.WithPiTopology

variable [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]

omit [TopologicalSpace K] [IsTopologicalRing K] [T2Space K] in
/-- Helper lemma: The coefficient of a product is zero if one factor has all low coefficients zero.
This is used in the proof of summability for product families. -/
lemma coeff_finProd_eq_zero_of_factor_high_order {n : ℕ} {S : Fin n → Type*}
    (p : (i : Fin n) → S i → K⟦X⟧)
    (f : (i : Fin n) → S i) (i : Fin n) (d : ℕ)
    (h : ∀ m ≤ d, coeff m (p i (f i)) = 0) :
    coeff d (∏ j : Fin n, p j (f j)) = 0 := by
  have h_order : (d : ℕ∞) < order (p i (f i)) := by
    have hle := nat_le_order (p i (f i)) (d + 1) (fun k hk => h k (Nat.lt_add_one_iff.mp hk))
    calc (d : ℕ∞) < d + 1 := by norm_cast; omega
      _ ≤ order (p i (f i)) := hle
  have h_prod_order : (d : ℕ∞) < order (∏ j : Fin n, p j (f j)) := by
    calc (d : ℕ∞) < order (p i (f i)) := h_order
      _ = ∑ j ∈ ({i} : Finset (Fin n)), order (p j (f j)) := by simp
      _ ≤ ∑ j : Fin n, order (p j (f j)) := by
          apply Finset.sum_le_sum_of_subset
          simp
      _ ≤ order (∏ j : Fin n, p j (f j)) := le_order_prod _ _
  exact coeff_of_lt_order d h_prod_order

omit [IsTopologicalRing K] [T2Space K] in
/-- **Summability of finite product families** (discrete case)

For discrete `K`, the family `f ↦ ∏ i, p i (f i)` is summable when each `p i` is summable.
This is the key technical lemma for `prod_tsum_eq_tsum_prod_finset`.

**Proof strategy**: For each coefficient `d`, only finitely many `f` contribute:
- Define `T i` = union of supports of `coeff m ∘ (p i)` for `m ≤ d`
- Each `T i` is finite (by discrete summability)
- The set `{f | ∀ i, f i ∈ T i}` is finite (product of finite sets)
- If `f i ∉ T i` for some `i`, then `coeff d (∏ j, p j (f j)) = 0`

This proves that the support of `f ↦ coeff d (∏ i, p i (f i))` is finite. -/
lemma summable_finProd_discrete [DiscreteTopology K] {n : ℕ} {S : Fin n → Type*}
    (p : (i : Fin n) → S i → K⟦X⟧)
    (hp : ∀ i, Summable (p i)) :
    Summable (fun f : (i : Fin n) → S i => ∏ i : Fin n, p i (f i)) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro d
  apply summable_of_hasFiniteSupport
  -- Get finite support for each factor at each coefficient
  have hp_coeff : ∀ i m, (Function.support (fun k => coeff m (p i k))).Finite := by
    intro i m
    have := (PowerSeries.WithPiTopology.summable_iff_summable_coeff (f := p i)).mp (hp i) m
    exact this.hasFiniteSupport_of_discreteTopology
  -- Define the "relevant" elements for each i
  let T : (i : Fin n) → Set (S i) := fun i =>
    ⋃ m ∈ Iic d, Function.support (fun k => coeff m (p i k))
  have hT_finite : ∀ i, (T i).Finite := by
    intro i
    apply Set.Finite.biUnion (Iic d).finite_toSet
    intro m _
    exact hp_coeff i m
  -- The set {f | ∀ i, f i ∈ T i} is finite (product of finite sets)
  have h_finite : {f : (i : Fin n) → S i | ∀ i, f i ∈ T i}.Finite := Set.Finite.pi' hT_finite
  -- The support is contained in {f | ∀ i, f i ∈ T i}
  apply h_finite.subset
  intro f hf
  simp only [Function.mem_support, ne_eq, Set.mem_ofPred_eq] at hf ⊢
  intro i
  by_contra h_not_in
  have h_coeff_zero : ∀ m ≤ d, coeff m (p i (f i)) = 0 := by
    intro m hm
    by_contra hne
    apply h_not_in
    simp only [T, Set.mem_iUnion]
    exact ⟨m, Finset.mem_Iic.mpr hm, hne⟩
  exact hf (coeff_finProd_eq_zero_of_factor_high_order p f i d h_coeff_zero)

omit [IsTopologicalRing K] [T2Space K] in
/-- Product of two summable families in K⟦X⟧ is summable (discrete case).

This is used in the proof of `prod_tsum_eq_tsum_prod_finset_discrete`. -/
lemma summable_prod_of_summable_discrete [DiscreteTopology K] {α β : Type*}
    (f : α → K⟦X⟧) (g : β → K⟦X⟧)
    (hf : Summable f) (hg : Summable g) :
    Summable (fun p : α × β => f p.1 * g p.2) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro d
  simp only [coeff_mul]
  apply summable_of_hasFiniteSupport
  have hf_coeff : ∀ n, (Function.support (fun a => coeff n (f a))).Finite := by
    intro n
    have := (PowerSeries.WithPiTopology.summable_iff_summable_coeff (f := f)).mp hf n
    exact this.hasFiniteSupport_of_discreteTopology
  have hg_coeff : ∀ n, (Function.support (fun b => coeff n (g b))).Finite := by
    intro n
    have := (PowerSeries.WithPiTopology.summable_iff_summable_coeff (f := g)).mp hg n
    exact this.hasFiniteSupport_of_discreteTopology
  let S := ⋃ (p : ℕ × ℕ) (_ : p ∈ Finset.HasAntidiagonal.antidiagonal d), 
      (Function.support (fun a => coeff p.1 (f a))) ×ˢ 
      (Function.support (fun b => coeff p.2 (g b)))
  have hS_finite : S.Finite := by
    apply Set.Finite.biUnion (Finset.HasAntidiagonal.antidiagonal d).finite_toSet
    intro ⟨i, j⟩ _
    exact Set.Finite.prod (hf_coeff i) (hg_coeff j)
  apply hS_finite.subset
  intro ⟨a, b⟩ hab
  simp only [Function.mem_support, ne_eq] at hab ⊢
  simp only [S, Set.mem_iUnion, Set.mem_prod_eq, Function.mem_support, ne_eq]
  by_contra h_all_zero
  push Not at h_all_zero
  apply hab
  apply Finset.sum_eq_zero
  intro ⟨i, j⟩ hij
  by_cases hfi : coeff i (f a) = 0
  · simp [hfi]
  · have h := h_all_zero (i, j) hij hfi
    simp [h]

/-- Helper lemma: the tsum_mul_tsum formula with swapped order.
This is needed for the inductive step of the finite product rule. -/
lemma tsum_mul_tsum_eq_tsum_prod_swap {α β : Type*}
    (f : α → K⟦X⟧) (g : β → K⟦X⟧)
    (hf : Summable f) (hg : Summable g)
    (hfg : Summable (fun p : α × β => f p.1 * g p.2)) :
    (∑' a, f a) * (∑' b, g b) = ∑' p : β × α, f p.2 * g p.1 := by
  rw [hf.tsum_mul_tsum hg hfg]
  let e : β × α ≃ α × β := Equiv.prodComm β α
  calc ∑' (z : α × β), f z.1 * g z.2
      = ∑' (c : β × α), f (e c).1 * g (e c).2 := (e.tsum_eq _).symm
    _ = ∑' (c : β × α), f c.2 * g c.1 := by rfl

omit [TopologicalSpace K] [IsTopologicalRing K] [T2Space K] in
/-- If a factor in a finite product has all coefficients up to n equal to zero,
then the product also has coefficient n equal to zero.
(Local copy for use in summability proofs.) -/
lemma coeff_prod_eq_zero_of_factor_coeff_zero_aux
    {I : Type*} [DecidableEq I] (s : Finset I) (f : I → K⟦X⟧)
    (j : I) (hj : j ∈ s) (n : ℕ) (hf : ∀ m ≤ n, coeff m (f j) = 0) :
    ∀ m ≤ n, coeff m (∏ i ∈ s, f i) = 0 := by
  intro m hm
  have h_mul : ∃ g, ∏ i ∈ s, f i = f j * g := by
    use ∏ i ∈ s.erase j, f i
    rw [← Finset.prod_erase_mul s f hj, mul_comm]
  obtain ⟨g, hg⟩ := h_mul
  rw [hg, coeff_mul]
  apply Finset.sum_eq_zero
  intro ⟨a, b⟩ hab
  have ha : a ≤ m := by simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hab; omega
  rw [hf a (ha.trans hm), zero_mul]

omit [IsTopologicalRing K] [T2Space K] in
/-- For discrete K, summable power series families have finite support at each coefficient. -/
lemma summable_ps_finite_support_coeff [DiscreteTopology K] {α : Type*}
    (f : α → K⟦X⟧) (hf : Summable f) (d : ℕ) :
    (Function.support (fun a => coeff d (f a))).Finite := by
  have h := (PowerSeries.WithPiTopology.summable_iff_summable_coeff (f := f)).mp hf d
  exact h.hasFiniteSupport_of_discreteTopology

omit [IsTopologicalRing K] [T2Space K] in
/-- For discrete K, the product of two summable power series families is summable. -/
lemma summable_prod_of_summable [DiscreteTopology K] {α β : Type*}
    (f : α → K⟦X⟧) (g : β → K⟦X⟧)
    (hf : Summable f) (hg : Summable g) :
    Summable (fun p : α × β => f p.1 * g p.2) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro d
  apply summable_of_hasFiniteSupport
  classical
  let Tf : Set α := {a | ∃ i ≤ d, coeff i (f a) ≠ 0}
  let Tg : Set β := {b | ∃ j ≤ d, coeff j (g b) ≠ 0}
  have hTf_finite : Tf.Finite := by
    have h_union : Tf = ⋃ i ∈ Finset.Iic d, {a | coeff i (f a) ≠ 0} := by
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_Iic]
      constructor
      · intro ⟨i, hi, hne⟩; exact ⟨i, hi, hne⟩
      · intro ⟨i, hi, hne⟩; exact ⟨i, hi, hne⟩
    rw [h_union]
    apply Set.Finite.biUnion (Finset.Iic d).finite_toSet
    intro i _
    have h := summable_ps_finite_support_coeff f hf i
    exact h.subset (fun a ha => by simp only [Function.mem_support] at ha ⊢; exact ha)
  have hTg_finite : Tg.Finite := by
    have h_union : Tg = ⋃ j ∈ Finset.Iic d, {b | coeff j (g b) ≠ 0} := by
      ext b
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_Iic]
      constructor
      · intro ⟨j, hj, hne⟩; exact ⟨j, hj, hne⟩
      · intro ⟨j, hj, hne⟩; exact ⟨j, hj, hne⟩
    rw [h_union]
    apply Set.Finite.biUnion (Finset.Iic d).finite_toSet
    intro j _
    have h := summable_ps_finite_support_coeff g hg j
    exact h.subset (fun b hb => by simp only [Function.mem_support] at hb ⊢; exact hb)
  have h_support : Function.support (fun p : α × β => coeff d (f p.1 * g p.2)) ⊆ Tf ×ˢ Tg := by
    intro ⟨a, b⟩ hab
    simp only [Function.mem_support, ne_eq, Set.mem_prod] at hab ⊢
    constructor
    · by_contra h_not_in
      have h_coeff_zero : ∀ i ≤ d, coeff i (f a) = 0 := by
        intro i hi
        by_contra hne
        apply h_not_in
        exact ⟨i, hi, hne⟩
      rw [coeff_mul] at hab
      apply hab
      apply Finset.sum_eq_zero
      intro ⟨i, j⟩ hij
      have hi : i ≤ d := by simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hij; omega
      rw [h_coeff_zero i hi, zero_mul]
    · by_contra h_not_in
      have h_coeff_zero : ∀ j ≤ d, coeff j (g b) = 0 := by
        intro j hj
        by_contra hne
        apply h_not_in
        exact ⟨j, hj, hne⟩
      rw [coeff_mul] at hab
      apply hab
      apply Finset.sum_eq_zero
      intro ⟨i, j⟩ hij
      have hj : j ≤ d := by simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hij; omega
      rw [h_coeff_zero j hj, mul_zero]
  exact (hTf_finite.prod hTg_finite).subset h_support

omit [IsTopologicalRing K] [T2Space K] in
/-- For discrete K, a finite product of summable families is summable. -/
lemma summable_prod_fin [DiscreteTopology K] {n : ℕ} {S : Fin n → Type*}
    (p : (i : Fin n) → S i → K⟦X⟧)
    (hp : ∀ i, Summable (p i)) :
    Summable (fun f : (i : Fin n) → S i => ∏ i : Fin n, p i (f i)) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro d
  apply summable_of_hasFiniteSupport
  classical
  let T : (i : Fin n) → Set (S i) := fun i =>
    {k | ∃ m ≤ d, coeff m (p i k) ≠ 0}
  have hT_finite : ∀ i, (T i).Finite := by
    intro i
    have h_union : T i = ⋃ m ∈ Finset.Iic d, {k | coeff m (p i k) ≠ 0} := by
      ext k
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_Iic]
      constructor
      · intro ⟨m, hm, hne⟩; exact ⟨m, hm, hne⟩
      · intro ⟨m, hm, hne⟩; exact ⟨m, hm, hne⟩
    rw [h_union]
    apply Set.Finite.biUnion (Finset.Iic d).finite_toSet
    intro m _
    have h := summable_ps_finite_support_coeff (p i) (hp i) m
    exact h.subset (fun k hk => by simp only [Function.mem_support] at hk ⊢; exact hk)
  have h_support : Function.support (fun f : (i : Fin n) → S i => coeff d (∏ i, p i (f i))) ⊆
      {f | ∀ i, f i ∈ T i} := by
    intro f hf
    simp only [Function.mem_support, ne_eq, Set.mem_ofPred_eq] at hf ⊢
    intro i
    by_contra h_not_in
    have h_coeff_zero : ∀ m ≤ d, coeff m (p i (f i)) = 0 := by
      intro m hm
      by_contra hne
      apply h_not_in
      exact ⟨m, hm, hne⟩
    have h_prod_zero := coeff_prod_eq_zero_of_factor_coeff_zero_aux Finset.univ
      (fun j => p j (f j)) i (Finset.mem_univ i) d h_coeff_zero d (le_refl d)
    exact hf h_prod_zero
  have h_finite : {f : (i : Fin n) → S i | ∀ i, f i ∈ T i}.Finite := by
    exact Set.Finite.pi' hT_finite
  exact h_finite.subset h_support

set_option maxHeartbeats 400000 in
/-- **Finite Product Rule for Infinite Sums** (Proposition prop.fps.prodrule-fin-inf)

For a finite product of summable families:
`∏_{i=1}^n (∑_{k ∈ S_i} p_{i,k}) = ∑_{(k₁,...,k_n) ∈ S₁×...×S_n} ∏_{i=1}^n p_{i,k_i}`

(Proposition prop.fps.prodrule-fin-infJ is the version with general finite index set)

**Proof strategy**: By induction on n.
- Base case (n=0): Both sides equal 1.
- Inductive step: Split the product into first n factors and the last factor, use IH on
  the first n, then apply the multiplication rule for sums.

**Note**: This theorem requires `DiscreteTopology K`. This covers the main use cases
(integers, rationals, finite fields). For non-discrete `K` (like ℝ or ℂ), additional
assumptions (such as absolute summability) would be needed. -/
lemma prod_tsum_eq_tsum_prod_finset [DiscreteTopology K] {n : ℕ} {S : Fin n → Type*}
    (p : (i : Fin n) → S i → K⟦X⟧)
    (hp : ∀ i, Summable (p i)) :
    ∏ i : Fin n, ∑' k, p i k =
    ∑' f : (i : Fin n) → S i, ∏ i : Fin n, p i (f i) := by
  induction n with
  | zero =>
    -- Base case: empty product = 1, sum over unique element = 1
    simp
  | succ n ih =>
    -- Inductive step: split product using Fin.prod_univ_castSucc
    rw [Fin.prod_univ_castSucc]

    -- Apply IH to the first n factors
    have h1 : ∏ i : Fin n, ∑' k : S (Fin.castSucc i), p (Fin.castSucc i) k =
              ∑' f : (i : Fin n) → S (Fin.castSucc i), ∏ i : Fin n, p (Fin.castSucc i) (f i) := by
      exact ih (fun i => p (Fin.castSucc i)) (fun i => hp (Fin.castSucc i))

    rw [h1]

    -- Use the equivalence to rewrite the RHS
    let e := finSuccProdEquiv n S

    -- The product ∏ i, p i (e ⟨a, f⟩ i) = (∏ j, p (castSucc j) (f j)) * p (last n) a
    have hprod : ∀ (a : S (Fin.last n)) (f : (i : Fin n) → S (Fin.castSucc i)),
        ∏ i : Fin (n + 1), p i (e ⟨a, f⟩ i) =
        (∏ j : Fin n, p (Fin.castSucc j) (f j)) * p (Fin.last n) a := by
      intro a f
      rw [Fin.prod_univ_castSucc]
      congr 1
      · apply Finset.prod_congr rfl
        intro j _
        simp only [e, finSuccProdEquiv, Equiv.coe_fn_mk, Fin.lastCases_castSucc]
      · simp only [e, finSuccProdEquiv, Equiv.coe_fn_mk, Fin.lastCases_last]

    -- Reindex the RHS using e.symm
    rw [← e.tsum_eq]
    simp_rw [hprod]

    -- Now need: (∑' f, ∏ j, p (castSucc j) (f j)) * (∑' a, p (last n) a) =
    --           ∑' ⟨a, f⟩, (∏ j, p (castSucc j) (f j)) * p (last n) a
    -- This follows from the tsum_mul_tsum formula

    -- Establish summability of the product family using our helper lemmas
    have hf_summable : Summable (fun f : (i : Fin n) → S (Fin.castSucc i) =>
        ∏ j : Fin n, p (Fin.castSucc j) (f j)) :=
      summable_prod_fin (fun i => p (Fin.castSucc i)) (fun i => hp (Fin.castSucc i))

    have hg_summable : Summable (fun a : S (Fin.last n) => p (Fin.last n) a) :=
      hp (Fin.last n)

    have hfg_summable : Summable (fun pair : ((i : Fin n) → S (Fin.castSucc i)) × S (Fin.last n) =>
        (∏ j : Fin n, p (Fin.castSucc j) (pair.1 j)) * p (Fin.last n) pair.2) :=
      summable_prod_of_summable
        (α := (i : Fin n) → S (Fin.castSucc i))
        (β := S (Fin.last n))
        (fun f => ∏ j : Fin n, p (Fin.castSucc j) (f j))
        (fun a => p (Fin.last n) a)
        hf_summable hg_summable

    -- Apply the tsum_mul_tsum formula
    rw [tsum_mul_tsum_eq_tsum_prod_swap _ _ hf_summable hg_summable hfg_summable]

/-- Version with general finite index set.

**Note**: This theorem requires `DiscreteTopology K` to use `prod_tsum_eq_tsum_prod_finset`. -/
lemma prod_tsum_eq_tsum_prod_finset' [DiscreteTopology K] {N : Type*} [Fintype N] [DecidableEq N]
    {S : N → Type*}
    (p : (i : N) → S i → K⟦X⟧)
    (hp : ∀ i, Summable (p i)) :
    ∏ i : N, ∑' k, p i k =
    ∑' f : (i : N) → S i, ∏ i : N, p i (f i) := by
  -- Use the equivalence N ≃ Fin (Fintype.card N)
  let e := Fintype.equivFin N
  -- Apply the Fin version with S ∘ e.symm
  have h := @prod_tsum_eq_tsum_prod_finset K _ _ _ _ _ (Fintype.card N) (S ∘ e.symm)
      (fun i => p (e.symm i)) (fun i => hp (e.symm i))
  -- Transform using equivalences
  have lhs_eq : ∏ i : N, ∑' k, p i k =
                ∏ i : Fin (Fintype.card N), ∑' k : S (e.symm i), p (e.symm i) k := by
    rw [Fintype.prod_equiv e.symm]
    simp
  have rhs_eq : ∑' f : (i : N) → S i, ∏ i : N, p i (f i) =
                ∑' f : (i : Fin (Fintype.card N)) → S (e.symm i), ∏ i, p (e.symm i) (f i) := by
    rw [← (Equiv.piCongrLeft' S e).tsum_eq]
    congr 1
    ext f
    rw [Fintype.prod_equiv e.symm]
    simp only [Equiv.piCongrLeft'_apply]
    intro _
    trivial
  rw [lhs_eq, rhs_eq]
  exact h

set_option maxHeartbeats 400000 in
/-- **Finite Product Rule for Infinite Sums** (discrete case, fully proved)

For a finite product of summable families over `Fin n`:
`∏_{i=1}^n (∑_{k ∈ S_i} p_{i,k}) = ∑_{(k₁,...,k_n) ∈ S₁×...×S_n} ∏_{i=1}^n p_{i,k_i}`

This is the discrete topology version of `prod_tsum_eq_tsum_prod_finset`, with a complete proof.
The key insight is that in discrete topology, summability implies finite support for each
coefficient, which allows us to prove summability of the product family directly.

**Proof strategy**: By induction on n.
- Base case (n=0): Both sides equal 1.
- Inductive step: Split the product into first n factors and the last factor, use IH on
  the first n, then apply the multiplication rule for sums.
- Summability of the product family is proved using `summable_finProd_discrete` and
  `summable_prod_of_summable_discrete`. -/
lemma prod_tsum_eq_tsum_prod_finset_discrete [DiscreteTopology K] {n : ℕ} {S : Fin n → Type*}
    (p : (i : Fin n) → S i → K⟦X⟧)
    (hp : ∀ i, Summable (p i)) :
    ∏ i : Fin n, ∑' k, p i k =
    ∑' f : (i : Fin n) → S i, ∏ i : Fin n, p i (f i) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc]
    have h1 : ∏ i : Fin n, ∑' k : S (Fin.castSucc i), p (Fin.castSucc i) k =
              ∑' f : (i : Fin n) → S (Fin.castSucc i), ∏ i : Fin n, p (Fin.castSucc i) (f i) := by
      exact ih (fun i => p (Fin.castSucc i)) (fun i => hp (Fin.castSucc i))
    rw [h1]
    let e := finSuccProdEquiv n S
    have hprod : ∀ (a : S (Fin.last n)) (f : (i : Fin n) → S (Fin.castSucc i)),
        ∏ i : Fin (n + 1), p i (e ⟨a, f⟩ i) =
        (∏ j : Fin n, p (Fin.castSucc j) (f j)) * p (Fin.last n) a := by
      intro a f
      rw [Fin.prod_univ_castSucc]
      congr 1
      · apply Finset.prod_congr rfl
        intro j _
        simp only [e, finSuccProdEquiv, Equiv.coe_fn_mk, Fin.lastCases_castSucc]
      · simp only [e, finSuccProdEquiv, Equiv.coe_fn_mk, Fin.lastCases_last]
    rw [← e.tsum_eq]
    simp_rw [hprod]
    have hf_summable : Summable (fun f : (i : Fin n) → S (Fin.castSucc i) =>
        ∏ j : Fin n, p (Fin.castSucc j) (f j)) :=
      summable_finProd_discrete (fun i => p (Fin.castSucc i)) (fun i => hp (Fin.castSucc i))
    have hg_summable : Summable (fun a : S (Fin.last n) => p (Fin.last n) a) :=
      hp (Fin.last n)
    have hfg_summable : Summable (fun pair : ((i : Fin n) → S (Fin.castSucc i)) × S (Fin.last n) =>
        (∏ j : Fin n, p (Fin.castSucc j) (pair.1 j)) * p (Fin.last n) pair.2) := by
      let f' : ((i : Fin n) → S (Fin.castSucc i)) → K⟦X⟧ := 
        fun f => ∏ j : Fin n, p (Fin.castSucc j) (f j)
      let g' : S (Fin.last n) → K⟦X⟧ := fun a => p (Fin.last n) a
      exact summable_prod_of_summable_discrete f' g' hf_summable hg_summable
    rw [tsum_mul_tsum_eq_tsum_prod_swap _ _ hf_summable hg_summable hfg_summable]

/-- **Finite Product Rule for Infinite Sums** (discrete case, general finite index set)

This is `prop.fps.prodrule-fin-infJ` for discrete topology, fully proved.

For a finite product of summable families over any finite type N:
`∏_{i ∈ N} (∑_{k ∈ S_i} p_{i,k}) = ∑_{f : N → S} ∏_{i ∈ N} p_{i,f(i)}`

This version uses `prod_tsum_eq_tsum_prod_finset_discrete` and reindexes via `Fintype.equivFin`. -/
lemma prod_tsum_eq_tsum_prod_finset'_discrete [DiscreteTopology K] 
    {N : Type*} [Fintype N] [DecidableEq N]
    {S : N → Type*}
    (p : (i : N) → S i → K⟦X⟧)
    (hp : ∀ i, Summable (p i)) :
    ∏ i : N, ∑' k, p i k =
    ∑' f : (i : N) → S i, ∏ i : N, p i (f i) := by
  -- Use the equivalence N ≃ Fin (Fintype.card N)
  let e := Fintype.equivFin N
  -- Apply the Fin version with S ∘ e.symm
  have h := prod_tsum_eq_tsum_prod_finset_discrete (S := S ∘ e.symm)
      (fun i => p (e.symm i)) (fun i => hp (e.symm i))
  -- Transform using equivalences
  have lhs_eq : ∏ i : N, ∑' k, p i k =
                ∏ i : Fin (Fintype.card N), ∑' k : S (e.symm i), p (e.symm i) k := by
    rw [Fintype.prod_equiv e.symm]
    simp
  have rhs_eq : ∑' f : (i : N) → S i, ∏ i : N, p i (f i) =
                ∑' f : (i : Fin (Fintype.card N)) → S (e.symm i), ∏ i, p (e.symm i) (f i) := by
    rw [← (Equiv.piCongrLeft' S e).tsum_eq]
    congr 1
    ext f
    rw [Fintype.prod_equiv e.symm]
    simp only [Equiv.piCongrLeft'_apply]
    intro _
    trivial
  rw [lhs_eq, rhs_eq]
  exact h

/-- Finite product over a finset equals tsum over functions.

This is a variant of `prod_tsum_eq_tsum_prod_finset'_discrete` for products over a finset
rather than a fintype. Useful for expanding `∏ i ∈ s, ∑' k, p i k`. -/
lemma prod_finset_tsum_eq_tsum_prod [DiscreteTopology K]
    {I : Type*} [DecidableEq I] {S : I → Type*}
    (s : Finset I) (p : (i : I) → S i → K⟦X⟧) (hp : ∀ i ∈ s, Summable (p i)) :
    ∏ i ∈ s, ∑' k : S i, p i k = ∑' f : (i : s) → S i, ∏ i : s, p i (f i) := by
  conv_lhs => rw [← Finset.prod_attach]
  have h : ∏ x ∈ s.attach, ∑' (k : S ↑x), p (↑x) k = ∏ i : s, ∑' k : S i, p i k := by
    simp only [Finset.univ_eq_attach]
  rw [h]
  have hp' : ∀ i : s, Summable (fun k : S i => p i k) := fun i => hp i i.prop
  exact prod_tsum_eq_tsum_prod_finset'_discrete (fun i : s => p i) hp'

end FiniteProductInfiniteSums


section InfiniteProductRules

open scoped PowerSeries.WithPiTopology

variable [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]

omit [IsTopologicalRing K] [T2Space K] in
/-- For an essentially finite function f, the family (p i (f i))_i is multipliable
when p i 0 = 1 for all i. This is because f i = 0 for all but finitely many i,
so p i (f i) = p i 0 = 1 for all but finitely many i. -/
lemma multipliable_of_essentiallyFinite
    {I : Type*} {S : I → Type*} [∀ i, Zero (S i)] [∀ i, DecidableEq (S i)]
    (p : (i : I) → S i → K⟦X⟧)
    (hp_zero : ∀ i, p i 0 = 1)
    (f : { f : (i : I) → S i // ∀ᶠ i in Filter.cofinite, f i = 0 }) :
    Multipliable fun i => p i (f.val i) := by
  have h : ∀ᶠ i in Filter.cofinite, p i (f.val i) = 1 := by
    filter_upwards [f.prop] with i hi
    rw [hi, hp_zero]
  have hfin : (Function.mulSupport fun i => p i (f.val i)).Finite := by
    rw [Filter.eventually_cofinite] at h
    exact h
  exact multipliable_of_hasFiniteMulSupport hfin


omit [IsTopologicalRing K] [T2Space K] in
/-- For discrete K, a subfamily via injective map is summable.
This is used for proving that fibers of summable families are summable. -/
lemma summable_comp_injective_of_discrete [DiscreteTopology K] {α β : Type*}
    {f : α → K} (hf : Summable f) {g : β → α} (hg : Function.Injective g) :
    Summable (f ∘ g) := by
  apply summable_of_hasFiniteSupport
  have h : (Function.support (f ∘ g)) ⊆ g ⁻¹' (Function.support f) := by
    intro x hx
    simp only [Function.mem_support, Function.comp_apply, Set.mem_preimage] at hx ⊢
    exact hx
  exact Set.Finite.subset (hf.hasFiniteSupport_of_discreteTopology.preimage hg.injOn) h

omit [IsTopologicalRing K] [T2Space K] in
/-- For discrete K, T'_n = {(i,k) : k ≠ 0, ∃ m ≤ n, coeff m (p i k) ≠ 0} is finite.
This follows from coefficient-wise summability. -/
lemma T'n_finite_of_discrete [DiscreteTopology K]
    {I : Type*} {S : I → Type*} [∀ i, Zero (S i)] [∀ i, DecidableEq (S i)]
    (p : (i : I) → S i → K⟦X⟧)
    (hp_summable : Summable fun ik : Σ i, { k : S i // k ≠ 0 } => p ik.1 ik.2.1)
    (n : ℕ) :
    { ik : Σ i, { k : S i // k ≠ 0 } | ∃ m ≤ n, coeff m (p ik.1 ik.2.val) ≠ 0 }.Finite := by
  have hp_coeff : ∀ m, Summable fun ik : Σ i, { k : S i // k ≠ 0 } => coeff m (p ik.1 ik.2.1) :=
    fun m => (PowerSeries.WithPiTopology.summable_iff_summable_coeff _).mp hp_summable m
  have hp_finite : ∀ m, (Function.support fun ik : Σ i, { k : S i // k ≠ 0 } =>
      coeff m (p ik.1 ik.2.1)).Finite :=
    fun m => (hp_coeff m).hasFiniteSupport_of_discreteTopology
  have h_eq : { ik : Σ i, { k : S i // k ≠ 0 } | ∃ m ≤ n, coeff m (p ik.1 ik.2.val) ≠ 0 } =
      ⋃ m ∈ Finset.Iic n, Function.support fun ik : Σ i, { k : S i // k ≠ 0 } => coeff m (p ik.1 ik.2.1) := by
    ext ik
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Function.mem_support]
    constructor
    · rintro ⟨m, hm, hne⟩; exact ⟨m, Finset.mem_Iic.mpr hm, hne⟩
    · rintro ⟨m, hm, hne⟩; exact ⟨m, Finset.mem_Iic.mp hm, hne⟩
  rw [h_eq]
  exact Set.Finite.biUnion (Finset.Iic n).finite_toSet (fun m _ => hp_finite m)

omit [TopologicalSpace K] [IsTopologicalRing K] [T2Space K] in
/-- If a factor in a finite product has all coefficients up to n equal to zero,
then the product also has coefficient n equal to zero. -/
lemma coeff_prod_eq_zero_of_factor_coeff_zero
    {I : Type*} [DecidableEq I] (s : Finset I) (f : I → K⟦X⟧)
    (j : I) (hj : j ∈ s) (n : ℕ) (hf : ∀ m ≤ n, coeff m (f j) = 0) :
    ∀ m ≤ n, coeff m (∏ i ∈ s, f i) = 0 := by
  intro m hm
  have h_mul : ∃ g, ∏ i ∈ s, f i = f j * g := by
    use ∏ i ∈ s.erase j, f i
    rw [← Finset.prod_erase_mul s f hj, mul_comm]
  obtain ⟨g, hg⟩ := h_mul
  rw [hg, coeff_mul]
  apply Finset.sum_eq_zero
  intro ⟨a, b⟩ hab
  have ha : a ≤ m := by simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hab; omega
  rw [hf a (ha.trans hm), zero_mul]

/-- Essentially finite functions whose graph is contained in a finite set form a finite set.
This is the key combinatorial lemma for proving summability of the RHS. -/
lemma finite_funcs_with_graph_in_finite_set
    {I : Type*} {S : I → Type*} [∀ i, Zero (S i)] [∀ i, DecidableEq (S i)]
    (T : Set (Σ i, { k : S i // k ≠ 0 })) (hT : T.Finite) :
    { f : { f : (i : I) → S i // ∀ᶠ i in Filter.cofinite, f i = 0 } |
      ∀ i, (hi : f.val i ≠ 0) → ⟨i, ⟨f.val i, hi⟩⟩ ∈ T }.Finite := by
  classical
  -- Define the graph as a set
  let graphSet : { f : (i : I) → S i // ∀ᶠ i in Filter.cofinite, f i = 0 } →
      Set (Σ i, { k : S i // k ≠ 0 }) :=
    fun f => { ik | ∃ (h : f.val ik.1 ≠ 0), ik.2 = ⟨f.val ik.1, h⟩ }
  -- The graph determines f uniquely
  have h_inj : ∀ f g, graphSet f = graphSet g → f = g := by
    intro f g hfg
    ext i
    by_cases hfi : f.val i = 0
    · by_cases hgi : g.val i = 0
      · rw [hfi, hgi]
      · exfalso
        have hg_in : ⟨i, ⟨g.val i, hgi⟩⟩ ∈ graphSet g := ⟨hgi, rfl⟩
        rw [← hfg] at hg_in
        obtain ⟨hfi', heq⟩ := hg_in
        simp only [Subtype.mk.injEq] at heq
        rw [hfi] at heq
        exact hgi heq
    · by_cases hgi : g.val i = 0
      · exfalso
        have hf_in : ⟨i, ⟨f.val i, hfi⟩⟩ ∈ graphSet f := ⟨hfi, rfl⟩
        rw [hfg] at hf_in
        obtain ⟨hgi', heq⟩ := hf_in
        simp only [Subtype.mk.injEq] at heq
        rw [hgi] at heq
        exact hfi heq
      · have hf_in : ⟨i, ⟨f.val i, hfi⟩⟩ ∈ graphSet f := ⟨hfi, rfl⟩
        rw [hfg] at hf_in
        obtain ⟨hgi', heq⟩ := hf_in
        simp only [Subtype.mk.injEq] at heq
        exact heq
  -- For f in our set, graphSet f ⊆ T
  have h_sub : ∀ f ∈ { f | ∀ i, (hi : f.val i ≠ 0) → ⟨i, ⟨f.val i, hi⟩⟩ ∈ T },
      graphSet f ⊆ T := by
    intro f hf ik hik
    obtain ⟨h, heq⟩ := hik
    have heq' : ik = ⟨ik.1, ⟨f.val ik.1, h⟩⟩ := by
      ext
      · rfl
      · simp only [heq_eq_eq]
        exact heq
    rw [heq']
    exact hf ik.1 h
  -- The graphSet map is injective on our set
  have h_inj_on : Set.InjOn graphSet { f | ∀ i, (hi : f.val i ≠ 0) → ⟨i, ⟨f.val i, hi⟩⟩ ∈ T } := by
    intro f _ g _ hfg
    exact h_inj f g hfg
  -- The image is in the powerset of T, which is finite
  have h_image_finite : (graphSet '' { f | ∀ i, (hi : f.val i ≠ 0) → ⟨i, ⟨f.val i, hi⟩⟩ ∈ T }).Finite := by
    apply Set.Finite.subset (hT.powerset)
    intro s hs
    simp only [Set.mem_image] at hs
    obtain ⟨f, hf, rfl⟩ := hs
    exact h_sub f hf
  exact Set.Finite.of_finite_image h_image_finite h_inj_on


omit [IsTopologicalRing K] [T2Space K] in
/-- **Claim 1 from tex proof (discrete case)**: For each i ∈ I, the family (p_{i,k})_{k ∈ S_i} is summable.

This version is for discrete K, where the proof is straightforward using
`summable_comp_injective_of_discrete`. -/
lemma summable_fiber_discrete [DiscreteTopology K]
    {I : Type*} {S : I → Type*} [∀ i, Zero (S i)] [∀ i, DecidableEq (S i)]
    (p : (i : I) → S i → K⟦X⟧)
    (hp_summable : Summable fun ik : Σ i, { k : S i // k ≠ 0 } => p ik.1 ik.2.1)
    (i : I) : Summable (p i) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro n
  have hp_coeff : Summable fun ik : Σ i, { k : S i // k ≠ 0 } => coeff n (p ik.1 ik.2.1) := by
    exact (PowerSeries.WithPiTopology.summable_iff_summable_coeff _).mp hp_summable n
  let e : { k : S i // k ≠ 0 } → Σ j, { k : S j // k ≠ 0 } := fun k => ⟨i, k⟩
  have he_inj : Function.Injective e := by
    intro ⟨k1, hk1⟩ ⟨k2, hk2⟩ heq
    simp only [e, Sigma.mk.injEq] at heq
    obtain ⟨_, h2⟩ := heq
    simp only [heq_eq_eq] at h2
    exact h2
  have h_fiber : Summable (fun k : { k : S i // k ≠ 0 } => coeff n (p i k.1)) := by
    have h_eq : (fun k : { k : S i // k ≠ 0 } => coeff n (p i k.1)) =
                (fun ik : Σ j, { k : S j // k ≠ 0 } => coeff n (p ik.1 ik.2.1)) ∘ e := by
      ext k; rfl
    rw [h_eq]
    exact summable_comp_injective_of_discrete hp_coeff he_inj
  have h_zero_summable : Summable (fun k : S i => if k = 0 then coeff n (p i 0) else 0) := by
    apply summable_of_hasFiniteSupport
    apply Set.Finite.subset (Set.finite_singleton 0)
    intro k hk
    simp only [Function.mem_support, Set.mem_singleton_iff] at hk ⊢
    by_contra h
    simp [h] at hk
  have h_nonzero_summable : Summable (fun k : S i => if k = 0 then 0 else coeff n (p i k)) := by
    have h_eq : (fun k : S i => if k = 0 then 0 else coeff n (p i k)) =
        Set.indicator {k : S i | k ≠ 0} (fun k => coeff n (p i k)) := by
      ext k
      simp only [Set.indicator, Set.mem_ofPred_eq]
      split_ifs with h1 h2
      · exact (h2 h1).elim
      · rfl
      · rfl
    rw [h_eq, ← summable_subtype_iff_indicator]
    exact h_fiber
  have h_eq : (fun k : S i => coeff n (p i k)) =
      (fun k => if k = 0 then coeff n (p i 0) else 0) +
      (fun k => if k = 0 then 0 else coeff n (p i k)) := by
    ext k
    simp only [Pi.add_apply]
    split_ifs with h
    · simp [h]
    · ring
  rw [h_eq]
  exact h_zero_summable.add h_nonzero_summable

omit [IsTopologicalRing K] in
/-- For discrete K, the family (∑_{k ∈ S_i, k ≠ 0} p_{i,k})_{i ∈ I} is summable.
This is a key lemma for proving multipliability of the tsum fiber family. -/
lemma summable_tsum_nonzero_fiber_discrete [DiscreteTopology K]
    {I : Type*} {S : I → Type*} [∀ i, Zero (S i)] [∀ i, DecidableEq (S i)]
    (p : (i : I) → S i → K⟦X⟧)
    (hp_summable : Summable fun ik : Σ i, { k : S i // k ≠ 0 } => p ik.1 ik.2.1) :
    Summable fun i => ∑' k : { k : S i // k ≠ 0 }, p i k.1 := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro n
  have hp_coeff : Summable fun ik : Σ i, { k : S i // k ≠ 0 } => coeff n (p ik.1 ik.2.1) := by
    exact (PowerSeries.WithPiTopology.summable_iff_summable_coeff _).mp hp_summable n
  have h_fiber : ∀ i, Summable (fun k : { k : S i // k ≠ 0 } => coeff n (p i k.1)) := by
    intro i
    let e : { k : S i // k ≠ 0 } → Σ j, { k : S j // k ≠ 0 } := fun k => ⟨i, k⟩
    have he_inj : Function.Injective e := by
      intro ⟨k1, hk1⟩ ⟨k2, hk2⟩ heq
      simp only [e, Sigma.mk.injEq] at heq
      obtain ⟨_, h2⟩ := heq
      simp only [heq_eq_eq] at h2
      exact h2
    have h_eq : (fun k : { k : S i // k ≠ 0 } => coeff n (p i k.1)) =
                (fun ik : Σ j, { k : S j // k ≠ 0 } => coeff n (p ik.1 ik.2.1)) ∘ e := by
      ext k; rfl
    rw [h_eq]
    exact summable_comp_injective_of_discrete hp_coeff he_inj
  have h_tsum_coeff : ∀ i, coeff n (∑' k : { k : S i // k ≠ 0 }, p i k.1) =
      ∑' k : { k : S i // k ≠ 0 }, coeff n (p i k.1) := by
    intro i
    have h_summable : Summable (fun k : { k : S i // k ≠ 0 } => p i k.1) := by
      rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
      intro m
      let e : { k : S i // k ≠ 0 } → Σ j, { k : S j // k ≠ 0 } := fun k => ⟨i, k⟩
      have he_inj : Function.Injective e := by
        intro ⟨k1, hk1⟩ ⟨k2, hk2⟩ heq
        simp only [e, Sigma.mk.injEq] at heq
        obtain ⟨_, h2⟩ := heq
        simp only [heq_eq_eq] at h2
        exact h2
      have h_eq : (fun k : { k : S i // k ≠ 0 } => coeff m (p i k.1)) =
                  (fun ik : Σ j, { k : S j // k ≠ 0 } => coeff m (p ik.1 ik.2.1)) ∘ e := by
        ext k; rfl
      rw [h_eq]
      exact summable_comp_injective_of_discrete
        ((PowerSeries.WithPiTopology.summable_iff_summable_coeff _).mp hp_summable m) he_inj
    let coeffCLM : K⟦X⟧ →L[K] K := ⟨coeff n, WithPiTopology.continuous_coeff K n⟩
    exact coeffCLM.map_tsum h_summable
  simp_rw [h_tsum_coeff]
  apply summable_of_hasFiniteSupport
  have h_support : (Function.support fun i => ∑' k : { k : S i // k ≠ 0 }, coeff n (p i k.1)) ⊆
      Sigma.fst '' (Function.support fun ik : Σ i, { k : S i // k ≠ 0 } => coeff n (p ik.1 ik.2.1)) := by
    intro i hi
    simp only [Function.mem_support] at hi
    simp only [Set.mem_image]
    by_contra h_all_zero
    push Not at h_all_zero
    have h_tsum_zero : ∑' k : { k : S i // k ≠ 0 }, coeff n (p i k.1) = 0 := by
      have h_all : ∀ k : { k : S i // k ≠ 0 }, coeff n (p i k.1) = 0 := by
        intro ⟨k, hk⟩
        by_contra hne
        have hmem : (⟨i, ⟨k, hk⟩⟩ : Σ j, { k : S j // k ≠ 0 }) ∈
            Function.support (fun ik : Σ i, { k : S i // k ≠ 0 } => coeff n (p ik.1 ik.2.1)) := by
          simp only [Function.mem_support]
          exact hne
        exact h_all_zero ⟨i, ⟨k, hk⟩⟩ hmem rfl
      simp only [h_all, tsum_zero]
    exact hi h_tsum_zero
  exact Set.Finite.subset (hp_coeff.hasFiniteSupport_of_discreteTopology.image _) h_support

/-- Helper lemma: In a complete uniform additive group, indicator of summable is summable. -/
lemma Summable.indicator_complete {α R : Type*} [AddCommGroup R] [UniformSpace R]
    [IsUniformAddGroup R] [CompleteSpace R]
    {f : α → R} (hf : Summable f) (s : Set α) : Summable (s.indicator f) := by
  classical
  rw [summable_iff_cauchySeq_finset, cauchySeq_finset_iff_sum_vanishing]
  intro U hU
  have hf_cauchy := summable_iff_cauchySeq_finset.mp hf
  rw [cauchySeq_finset_iff_sum_vanishing] at hf_cauchy
  obtain ⟨t, ht⟩ := hf_cauchy U hU
  use t
  intro u hu
  have h_eq : ∑ x ∈ u, s.indicator f x = ∑ x ∈ u.filter (· ∈ s), f x := by
    rw [Finset.sum_indicator_eq_sum_filter]
  rw [h_eq]
  apply ht
  exact hu.mono_left (Finset.filter_subset _ _)

end InfiniteProductRules

section SummableFiberComplete


open scoped PowerSeries.WithPiTopology

variable [UniformSpace K] [IsUniformAddGroup K] [IsTopologicalRing K] [CompleteSpace K]

/-- **Claim 1 from tex proof**: For each i ∈ I, the family (p_{i,k})_{k ∈ S_i} is summable.

This follows from the assumption that (p_{i,k})_{(i,k) ∈ S̄} is summable, since
each subfamily is summable.

**Proof strategy**: The family (p i k)_{k ∈ S_i} is summable because:
1. The subfamily (p i k)_{k ∈ S_i, k ≠ 0} is summable (as a subfamily of the summable family)
2. Adding the term p i 0 preserves summability

The key steps are:
- Use `summable_iff_summable_coeff` to reduce to coefficient-wise summability
- For each coefficient, use `Summable.indicator_complete` to show the fiber is summable
- Split the sum at k = 0 and combine

**Note**: This proof requires `CompleteSpace K` because subfamilies of summable families
are only guaranteed to be summable in complete spaces. For the discrete topology case,
use `summable_fiber_discrete` instead (which doesn't require completeness). -/
lemma summable_fiber
    {I : Type*} {S : I → Type*} [∀ i, Zero (S i)] [∀ i, DecidableEq (S i)]
    (p : (i : I) → S i → K⟦X⟧)
    (hp_summable : Summable fun ik : Σ i, { k : S i // k ≠ 0 } => p ik.1 ik.2.1)
    (i : I) : Summable (p i) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro n
  -- Get coefficient-wise summability from hp_summable
  have hp_coeff : Summable fun ik : Σ i, { k : S i // k ≠ 0 } => coeff n (p ik.1 ik.2.1) := by
    exact (PowerSeries.WithPiTopology.summable_iff_summable_coeff _).mp hp_summable n

  -- The fiber {k : S i // k ≠ 0} corresponds to a subset of the sigma type
  let fiber_set : Set (Σ j, { k : S j // k ≠ 0 }) := { ik | ik.1 = i }

  -- Define the function on the sigma type
  let g : (Σ j, { k : S j // k ≠ 0 }) → K := fun ik => coeff n (p ik.1 ik.2.1)

  -- The restriction to the fiber is summable by indicator lemma
  have h_fiber_indicator : Summable (fiber_set.indicator g) := hp_coeff.indicator_complete fiber_set

  -- The indicator restricted to fiber_set is summable
  have h_subtype : Summable (fun ik : fiber_set => g ik.val) := by
    have h : (fun ik : fiber_set => g ik.val) = g ∘ Subtype.val := rfl
    rw [h, summable_subtype_iff_indicator]
    exact h_fiber_indicator

  -- Convert this to summability over { k : S i // k ≠ 0 }
  have h_fiber : Summable (fun k : { k : S i // k ≠ 0 } => coeff n (p i k.1)) := by
    -- Use the equivalence between the fiber and the subtype
    let e : { k : S i // k ≠ 0 } ≃ fiber_set := {
      toFun := fun k => ⟨⟨i, k⟩, rfl⟩
      invFun := fun ⟨⟨j, k⟩, hj⟩ => by
        simp only [Set.mem_ofPred_eq, fiber_set] at hj
        subst hj
        exact k
      left_inv := fun k => rfl
      right_inv := fun ⟨⟨j, k⟩, hj⟩ => by
        simp only [Set.mem_ofPred_eq, fiber_set] at hj
        subst hj
        rfl
    }
    -- Use Equiv.summable_iff
    have h_eq : (fun k : { k : S i // k ≠ 0 } => coeff n (p i k.1)) =
                (fun ik : fiber_set => g ik.val) ∘ e := by
      ext k; rfl
    rw [h_eq, e.summable_iff]
    exact h_subtype

  -- Now extend from {k ≠ 0} to all of S i
  have h_zero_summable : Summable (fun k : S i => if k = 0 then coeff n (p i 0) else 0) := by
    apply summable_of_hasFiniteSupport
    apply Set.Finite.subset (Set.finite_singleton 0)
    intro k hk
    simp only [Function.mem_support, Set.mem_singleton_iff] at hk ⊢
    by_contra h
    simp [h] at hk

  have h_nonzero_summable : Summable (fun k : S i => if k = 0 then 0 else coeff n (p i k)) := by
    have h_eq : (fun k : S i => if k = 0 then 0 else coeff n (p i k)) =
        Set.indicator {k : S i | k ≠ 0} (fun k => coeff n (p i k)) := by
      ext k
      simp only [Set.indicator, Set.mem_ofPred_eq]
      split_ifs with h1 h2
      · exact (h2 h1).elim
      · rfl
      · rfl
    rw [h_eq, ← summable_subtype_iff_indicator]
    exact h_fiber

  have h_eq : (fun k : S i => coeff n (p i k)) =
      (fun k => if k = 0 then coeff n (p i 0) else 0) +
      (fun k => if k = 0 then 0 else coeff n (p i k)) := by
    ext k
    simp only [Pi.add_apply]
    split_ifs with h
    · simp [h]
    · ring
  rw [h_eq]
  exact h_zero_summable.add h_nonzero_summable

end SummableFiberComplete

section InfiniteProductRules

open scoped PowerSeries.WithPiTopology

variable [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]

/-- **Claim 2 from tex proof (discrete case)**: The family (∑_{k ∈ S_i} p_{i,k})_{i ∈ I} is multipliable.

For discrete K, this follows from coefficient-wise finiteness arguments. The key insight is that
∑_k p_{i,k} = 1 + ∑_{k≠0} p_{i,k}, and for discrete K, only finitely many finsets of indices
contribute to each coefficient of the partial products. -/
lemma multipliable_tsum_fiber_discrete [DiscreteTopology K]
    {I : Type*} {S : I → Type*} [∀ i, Zero (S i)] [∀ i, DecidableEq (S i)]
    (p : (i : I) → S i → K⟦X⟧)
    (hp_zero : ∀ i, p i 0 = 1)
    (hp_summable : Summable fun ik : Σ i, { k : S i // k ≠ 0 } => p ik.1 ik.2.1) :
    Multipliable fun i => ∑' k : S i, p i k := by
  -- Get coefficient-wise summability
  have hp_coeff : ∀ m, Summable fun ik : Σ i, { k : S i // k ≠ 0 } => coeff m (p ik.1 ik.2.1) :=
    fun m => (PowerSeries.WithPiTopology.summable_iff_summable_coeff _).mp hp_summable m

  -- For discrete K, summability implies finite support
  have hp_finite : ∀ m, (Function.support fun ik : Σ i, { k : S i // k ≠ 0 } =>
      coeff m (p ik.1 ik.2.1)).Finite :=
    fun m => (hp_coeff m).hasFiniteSupport_of_discreteTopology

  -- Each fiber is summable (use summable_fiber_discrete)
  have hp_summable_i : ∀ i, Summable (p i) := fun i => summable_fiber_discrete p hp_summable i

  -- Key: ∑' k, p i k = 1 + ∑' k : {k // k ≠ 0}, p i k.val
  have htsum_split : ∀ i, ∑' k : S i, p i k = p i 0 + ∑' k : S i, if k = 0 then 0 else p i k := by
    intro i; exact (hp_summable_i i).tsum_eq_add_tsum_ite 0

  simp_rw [htsum_split, hp_zero]

  have htsum_nonzero : ∀ i, ∑' k : S i, (if k = 0 then 0 else p i k) =
                           ∑' k : { k : S i // k ≠ 0 }, p i k.val := by
    intro i
    rw [← tsum_subtype_eq_of_support_subset]
    · congr 1; funext k; have hk : (k : S i) ≠ 0 := k.prop; simp only [hk, ↓reduceIte]
    · intro k hk; simp only [Function.mem_support] at hk ⊢
      intro h; rw [h, ite_eq_left rfl] at hk; exact hk rfl

  have heq : (fun i => 1 + ∑' k : S i, if k = 0 then 0 else p i k) =
             (fun i => 1 + ∑' k : { k : S i // k ≠ 0 }, p i k.val) := by
    ext i; rw [htsum_nonzero i]
  rw [heq]

  -- Use multipliable_one_add_of_summable_prod
  apply multipliable_one_add_of_summable_prod

  -- Need: Summable (fun s : Finset I => ∏ i ∈ s, ∑' k : {k // k ≠ 0}, p i k.val)
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro n
  apply summable_of_hasFiniteSupport
  classical

  -- Define T'_n and I_n
  let T'n : Set (Σ i, { k : S i // k ≠ 0 }) := { ik | ∃ m ≤ n, coeff m (p ik.1 ik.2.val) ≠ 0 }

  have hT'n_finite : T'n.Finite := T'n_finite_of_discrete p hp_summable n

  let I_n : Set I := { i | ∃ k : { k : S i // k ≠ 0 }, ⟨i, k⟩ ∈ T'n }

  have hI_n_finite : I_n.Finite := by
    have h : I_n ⊆ Sigma.fst '' T'n := fun i hi => by
      obtain ⟨k, hk⟩ := hi; exact ⟨⟨i, k⟩, hk, rfl⟩
    exact Set.Finite.subset (hT'n_finite.image _) h

  -- The support is contained in the powerset of I_n
  have h_support : Function.support (fun s : Finset I => coeff n (∏ i ∈ s, ∑' k : { k : S i // k ≠ 0 }, p i k.val)) ⊆
      {s : Finset I | ↑s ⊆ I_n} := by
    intro s hs
    simp only [Function.mem_support, ne_eq, Set.mem_ofPred_eq] at hs ⊢
    intro i hi
    by_contra h_not_in
    -- If i ∉ I_n, then for all k ≠ 0, coeff m (p i k) = 0 for m ≤ n
    have h_coeff_zero : ∀ k : { k : S i // k ≠ 0 }, ∀ m ≤ n, coeff m (p i k.val) = 0 := by
      intro ⟨k, hk⟩ m hm
      by_contra hne
      apply h_not_in
      simp only [I_n, Set.mem_ofPred_eq]
      exact ⟨⟨k, hk⟩, ⟨m, hm, hne⟩⟩
    -- The fiber sum has all coefficients up to n zero
    have h_fiber_summable : Summable (fun k : { k : S i // k ≠ 0 } => p i k.val) := by
      rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
      intro j
      let e : { k : S i // k ≠ 0 } → Σ l, { k : S l // k ≠ 0 } := fun k => ⟨i, k⟩
      have he_inj : Function.Injective e := by
        intro ⟨k1, hk1⟩ ⟨k2, hk2⟩ heq
        simp only [e, Sigma.mk.injEq] at heq
        obtain ⟨_, h2⟩ := heq; simp only [heq_eq_eq] at h2; exact h2
      apply summable_of_hasFiniteSupport
      have h : (Function.support (fun k : { k : S i // k ≠ 0 } => coeff j (p i k.val))) ⊆
          e ⁻¹' (Function.support (fun ik : Σ l, { k : S l // k ≠ 0 } => coeff j (p ik.1 ik.2.1))) := by
        intro x hx; simp only [Function.mem_support, Set.mem_preimage] at hx ⊢; exact hx
      exact Set.Finite.subset ((hp_finite j).preimage he_inj.injOn) h
    have h_tsum_order : ∀ m ≤ n, coeff m (∑' k : { k : S i // k ≠ 0 }, p i k.val) = 0 := by
      intro m hm
      have h_map : coeff m (∑' k : { k : S i // k ≠ 0 }, p i k.val) =
          ∑' k : { k : S i // k ≠ 0 }, coeff m (p i k.val) := by
        let coeffCLM : K⟦X⟧ →L[K] K := ⟨coeff m, WithPiTopology.continuous_coeff K m⟩
        exact coeffCLM.map_tsum h_fiber_summable
      rw [h_map]
      have h_all_zero : ∀ k : { k : S i // k ≠ 0 }, coeff m (p i k.val) = 0 := fun k => h_coeff_zero k m hm
      simp only [h_all_zero, tsum_zero]
    -- The product has a factor with all coefficients up to n zero
    have h_prod_eq : ∃ g, ∏ j ∈ s, ∑' k : { k : S j // k ≠ 0 }, p j k.val =
        (∑' k : { k : S i // k ≠ 0 }, p i k.val) * g := by
      use ∏ j ∈ s.erase i, ∑' k : { k : S j // k ≠ 0 }, p j k.val
      rw [← Finset.prod_erase_mul s (fun j => ∑' k : { k : S j // k ≠ 0 }, p j k.val) hi, mul_comm]
    obtain ⟨g, hg⟩ := h_prod_eq
    rw [hg] at hs
    rw [coeff_mul] at hs
    have h_all_zero : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal n,
        coeff x.1 (∑' k : { k : S i // k ≠ 0 }, p i k.val) * coeff x.2 g = 0 := by
      intro x hx
      have hx1_le : x.1 ≤ n := by simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hx; omega
      rw [h_tsum_order x.1 hx1_le, zero_mul]
    simp only [Finset.sum_eq_zero h_all_zero, ne_eq, not_true_eq_false] at hs

  -- The set of finsets contained in I_n is finite
  have h_finsets_finite : {s : Finset I | ↑s ⊆ I_n}.Finite := by
    obtain ⟨I_n', hI_n'⟩ := hI_n_finite.exists_finset_coe
    have : {t : Finset I | ↑t ⊆ I_n} = {t : Finset I | t ⊆ I_n'} := by
      ext t; simp only [Set.mem_ofPred_eq, ← hI_n', Finset.coe_subset]
    rw [this]
    exact I_n'.powerset.finite_toSet.subset (fun t ht => by simpa using ht)

  exact h_finsets_finite.subset h_support

omit [IsTopologicalRing K] [T2Space K] in
/-- **Claim 7 from tex proof** (discrete case): The family (∏_i p_{i,k_i})_{(k_i) ∈ S^I_fin} is summable.

For discrete K, this follows from the finiteness of T'_n and the helper lemmas above. -/
lemma summable_prod_essentiallyFinite_discrete [DiscreteTopology K]
    {I : Type*} {S : I → Type*} [∀ i, Zero (S i)] [∀ i, DecidableEq (S i)]
    (p : (i : I) → S i → K⟦X⟧)
    (hp_zero : ∀ i, p i 0 = 1)
    (hp_summable : Summable fun ik : Σ i, { k : S i // k ≠ 0 } => p ik.1 ik.2.1) :
    Summable fun f : { f : (i : I) → S i // ∀ᶠ i in Filter.cofinite, f i = 0 } =>
      ∏' i : I, p i (f.val i) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro n
  apply summable_of_hasFiniteSupport
  classical
  let T'n : Set (Σ i, { k : S i // k ≠ 0 }) :=
    { ik | ∃ m ≤ n, coeff m (p ik.1 ik.2.val) ≠ 0 }
  have hT'n_finite : T'n.Finite := T'n_finite_of_discrete p hp_summable n

  have h_support : Function.support (fun f : { f : (i : I) → S i // ∀ᶠ i in Filter.cofinite, f i = 0 } =>
      coeff n (∏' i : I, p i (f.val i))) ⊆
      { f | ∀ i, (hi : f.val i ≠ 0) → ⟨i, ⟨f.val i, hi⟩⟩ ∈ T'n } := by
    intro f hf
    simp only [Function.mem_support, ne_eq] at hf
    simp only [Set.mem_ofPred_eq]
    intro i hi
    by_contra h_not_in
    have h_coeff_zero : ∀ m ≤ n, coeff m (p i (f.val i)) = 0 := by
      intro m hm
      by_contra hne
      apply h_not_in
      exact ⟨m, hm, hne⟩
    have htprod_eq : ∏' j : I, p j (f.val j) = ∏ j ∈ f.prop.toFinset, p j (f.val j) := by
      have h : ∀ᶠ j in Filter.cofinite, p j (f.val j) = 1 := by
        filter_upwards [f.prop] with j hj
        rw [hj, hp_zero]
      have hfin : (Function.mulSupport fun j => p j (f.val j)).Finite :=
        Filter.eventually_cofinite.mp h
      have hsub : hfin.toFinset ⊆ f.prop.toFinset := by
        intro j hj'
        rw [hfin.mem_toFinset, Function.mem_mulSupport] at hj'
        rw [f.prop.mem_toFinset]
        intro heq; rw [heq, hp_zero] at hj'; exact hj' rfl
      rw [tprod_eq_prod' (fun x hx => hfin.mem_toFinset.mpr hx)]
      apply Finset.prod_subset hsub
      intro j _ hnj
      rw [hfin.mem_toFinset, Function.mem_mulSupport, not_not] at hnj
      exact hnj
    have hi_in : i ∈ f.prop.toFinset := by
      rw [f.prop.mem_toFinset]
      exact hi
    rw [htprod_eq] at hf
    have h_prod_zero := coeff_prod_eq_zero_of_factor_coeff_zero f.prop.toFinset
        (fun j => p j (f.val j)) i hi_in n h_coeff_zero n (le_refl n)
    exact hf h_prod_zero

  exact (finite_funcs_with_graph_in_finite_set T'n hT'n_finite).subset h_support

omit [IsTopologicalRing K] [T2Space K] in
/-- **Claim 7 from tex proof**: The family (∏_i p_{i,k_i})_{(k_i) ∈ S^I_fin} is summable.

This is the key summability result for the RHS. The proof shows that for each n,
only finitely many essentially finite families (k_i) contribute to the n-th coefficient.

**Proof strategy** (following the tex source):

1. Use `summable_iff_summable_coeff` to reduce to coefficient-wise summability.

2. For each coefficient n, define T'_n = { (i,k) : k ≠ 0, ∃ m ≤ n, coeff m (p i k) ≠ 0 }.
   This set is finite because hp_summable implies coefficient-wise summability.

3. Define ValidFun_n = { f essentially finite | graph(f) ⊆ T'_n }.
   This set is finite because it injects into the powerset of T'_n.

4. Show that if f ∉ ValidFun_n, then coeff n (∏' i, p i (f.val i)) = 0.
   This uses the irrelevance lemma: if (i, f i) ∉ T'_n for some i with f i ≠ 0,
   then p i (f i) = 1 + (terms of order > n), so the n-th coefficient is unaffected.

5. Apply `summable_of_hasFiniteSupport` to conclude.

**Note**: The proof requires discrete topology on K to show T'_n is finite via
`Summable.hasFiniteSupport_of_discreteTopology`. For general topological rings,
the finiteness of T'_n from coefficient-wise summability would need additional
structure beyond T2Space. -/
lemma summable_prod_essentiallyFinite [DiscreteTopology K] {I : Type*} {S : I → Type*}
    [∀ i, Zero (S i)] [∀ i, DecidableEq (S i)]
    (p : (i : I) → S i → K⟦X⟧)
    (hp_zero : ∀ i, p i 0 = 1)
    (hp_summable : Summable fun ik : Σ i, { k : S i // k ≠ 0 } => p ik.1 ik.2.1) :
    Summable fun f : { f : (i : I) → S i // ∀ᶠ i in Filter.cofinite, f i = 0 } =>
      ∏' i : I, p i (f.val i) :=
  summable_prod_essentiallyFinite_discrete p hp_zero hp_summable


section HelperLemmas

open Filter Topology

omit [TopologicalSpace K] [IsTopologicalRing K] [T2Space K] in
/-- For a finite product where extra factors have high order, the coeff n is unchanged.
If `s ⊆ t` and for all `i ∈ t \ s`, `g i` has all coefficients up to n equal to 0,
then `coeff n (∏ i ∈ t, (1 + g i)) = coeff n (∏ i ∈ s, (1 + g i))`.

This is a key helper for reducing infinite products to finite products when computing
individual coefficients. -/
lemma coeff_prod_eq_of_extra_high_order' {I : Type*} [DecidableEq I]
    (g : I → K⟦X⟧) (s t : Finset I) (hst : s ⊆ t)
    (n : ℕ) (h_high_order : ∀ i ∈ t \ s, ∀ m ≤ n, coeff m (g i) = 0) :
    coeff n (∏ i ∈ t, (1 + g i)) = coeff n (∏ i ∈ s, (1 + g i)) := by
  have h_disjoint : Disjoint s (t \ s) := disjoint_sdiff_self_right
  have h_union : s ∪ (t \ s) = t := union_sdiff_of_subset hst
  rw [← h_union, prod_union h_disjoint]
  have h_extra_eq_one : ∀ m ≤ n, coeff m (∏ i ∈ t \ s, (1 + g i)) = coeff m (1 : K⟦X⟧) := by
    intro m hm
    rw [prod_one_add]
    simp only [map_sum]
    rw [sum_eq_single ∅]
    · simp
    · intro u hu_mem hu
      obtain ⟨j, hj⟩ := nonempty_iff_ne_empty.mpr hu
      have hju : j ∈ t \ s := (mem_powerset.mp hu_mem) hj
      have h_order_j : ∀ k ≤ n, coeff k (g j) = 0 := h_high_order j hju
      have h_order_prod : (m : ℕ∞) < order (∏ i ∈ u, g i) := by
        have h_order_gj : (n : ℕ∞) < order (g j) := by
          have h := nat_le_order (g j) (n + 1) (fun k hk => h_order_j k (Nat.lt_add_one_iff.mp hk))
          calc (n : ℕ∞) < n + 1 := by norm_cast; omega
            _ ≤ (g j).order := h
        calc (m : ℕ∞) ≤ n := by exact_mod_cast hm
          _ < order (g j) := h_order_gj
          _ = ∑ i ∈ ({j} : Finset I), order (g i) := by simp
          _ ≤ ∑ i ∈ u, order (g i) := sum_le_sum_of_subset (by simp [hj])
          _ ≤ order (∏ i ∈ u, g i) := le_order_prod _ _
      exact coeff_of_lt_order m h_order_prod
    · intro h
      exact (h (empty_mem_powerset _)).elim
  rw [coeff_mul]
  conv_rhs => rw [← mul_one (∏ i ∈ s, (1 + g i)), coeff_mul]
  apply sum_congr rfl
  intro ⟨a, b⟩ hab
  have hb : b ≤ n := by have := mem_antidiagonal.mp hab; omega
  rw [h_extra_eq_one b hb]

omit [TopologicalSpace K] [IsTopologicalRing K] [T2Space K] in
/-- For infinite products, if `g i` has high order for `i ∉ I_n`,
then `coeff n` of the tprod equals `coeff n` of the finite product over `I_n`.

This is the key lemma for reducing infinite products to finite products
when computing individual coefficients. It implements Claim 10 from the tex proof. -/
lemma coeff_tprod_one_add_eq_coeff_prod_of_high_order' [TopologicalSpace K] [DiscreteTopology K]
    {I : Type*} (g : I → K⟦X⟧) (I_n : Set I) (hI_n : I_n.Finite)
    (hmult : Multipliable (1 + g ·))
    (n : ℕ) (h_high_order : ∀ i ∉ I_n, ∀ m ≤ n, coeff m (g i) = 0) :
    coeff n (∏' i, (1 + g i)) = coeff n (∏ i ∈ hI_n.toFinset, (1 + g i)) := by
  classical
  have htend : Tendsto (fun s => ∏ i ∈ s, (1 + g i)) atTop (nhds (∏' i, (1 + g i))) :=
    hmult.hasProd
  have hcoeff_cont : Continuous (coeff (R := K) n) := WithPiTopology.continuous_coeff K n
  have htend_coeff : Tendsto (fun s => coeff n (∏ i ∈ s, (1 + g i))) atTop
      (nhds (coeff n (∏' i, (1 + g i)))) := hcoeff_cont.continuousAt.tendsto.comp htend
  have h_eventually : ∀ s ≥ hI_n.toFinset,
      coeff n (∏ i ∈ s, (1 + g i)) = coeff n (∏ i ∈ hI_n.toFinset, (1 + g i)) := by
    intro s hs
    apply coeff_prod_eq_of_extra_high_order' g hI_n.toFinset s hs n
    intro i hi m hm
    have hi' : i ∉ I_n := by
      intro h
      have : i ∈ hI_n.toFinset := hI_n.mem_toFinset.mpr h
      exact (mem_sdiff.mp hi).2 this
    exact h_high_order i hi' m hm
  exact tendsto_nhds_unique htend_coeff
    (tendsto_atTop_of_eventually_const (i₀ := hI_n.toFinset) h_eventually)

end HelperLemmas


section ExtensionRestriction

variable {I : Type*} {S : I → Type*} [∀ i, Zero (S i)]

/-- Extension followed by restriction is the identity. -/
lemma restrictToI_n_extendToI_subtype {I_n : Set I} (hI_n_finite : I_n.Finite)
    (f : (i : hI_n_finite.toFinset) → S i) :
    restrictToI_n hI_n_finite (extendToI_subtype hI_n_finite f) = f := by
  classical
  ext ⟨i, hi⟩
  simp only [restrictToI_n, extendToI_subtype, extendToI, dite_eq_left hi]

/-- For f with support in I_n, restriction followed by extension is the identity. -/
lemma extendToI_subtype_restrictToI_n {I_n : Set I} (hI_n_finite : I_n.Finite)
    (f : { f : (i : I) → S i // ∀ᶠ i in Filter.cofinite, f i = 0 })
    (hf_supp : ∀ i, f.val i ≠ 0 → i ∈ I_n) :
    extendToI_subtype hI_n_finite (restrictToI_n hI_n_finite f) = f := by
  classical
  ext i
  simp only [extendToI_subtype, extendToI, restrictToI_n]
  by_cases hi : i ∈ hI_n_finite.toFinset
  · simp only [dite_eq_left hi]
  · simp only [dite_eq_right hi]
    by_contra hne
    apply hi
    rw [Set.Finite.mem_toFinset]
    exact hf_supp i (Ne.symm hne)

omit [IsTopologicalRing K] [T2Space K] in
/-- The finite product on I_n equals the tprod on I (after extension).
This is key for showing the bijection preserves products. -/
lemma prod_eq_tprod_extendToI {I_n : Set I} (hI_n_finite : I_n.Finite)
    (p : (i : I) → S i → K⟦X⟧)
    (hp_zero : ∀ i, p i 0 = 1)
    (f : (i : hI_n_finite.toFinset) → S i) :
    ∏ i : hI_n_finite.toFinset, p i (f i) =
    ∏' i : I, p i (extendToI hI_n_finite f i) := by
  classical
  -- The tprod is multipliable because all but finitely many factors are 1
  have h_mult : Multipliable fun i => p i (extendToI hI_n_finite f i) := by
    apply multipliable_of_hasFiniteMulSupport
    apply Set.Finite.subset hI_n_finite.toFinset.finite_toSet
    intro i hi
    simp only [Function.mem_mulSupport] at hi
    by_contra h_not_in
    simp only [Finset.mem_coe] at h_not_in
    unfold extendToI at hi
    rw [dite_eq_right h_not_in] at hi
    exact hi (hp_zero i)
  -- Convert tprod to finite product
  symm
  rw [tprod_eq_prod' (s := hI_n_finite.toFinset) (fun i hi => ?_)]
  · rw [← Finset.prod_attach]
    apply Finset.prod_congr rfl
    intro ⟨i, hi⟩ _
    unfold extendToI
    rw [dite_eq_left hi]
  · simp only [Function.mem_mulSupport, extendToI] at hi
    split_ifs at hi with h
    · exact h
    · exact (hi (hp_zero i)).elim

end ExtensionRestriction

omit [TopologicalSpace K] [IsTopologicalRing K] [T2Space K] in
/-- **General Infinite Product Rule** (Proposition prop.fps.prodrule-inf-inf)

For any index set `I`, let `(S_i)_{i ∈ I}` be sets that all contain `0`.
For `p_{i,k} ∈ K⟦X⟧` with `p_{i,0} = 1`, if the family `(p_{i,k})_{(i,k) ∈ S̄}` is summable, then:

`∏_{i ∈ I} (∑_{k ∈ S_i} p_{i,k}) = ∑_{essentially finite (k_i)_{i ∈ I}} ∏_{i ∈ I} p_{i,k_i}`

The key insight is that only essentially finite families contribute to the sum on the RHS,
ensuring that each product `∏_{i ∈ I} p_{i,k_i}` is well-defined (since all but finitely
many factors are `p_{i,0} = 1`).

**Proof status**: This theorem requires substantial infrastructure:
- `prod_tsum_eq_tsum_prod_finset'_discrete`: finite product of infinite sums (fully proved)
- `coeff_mul_tprod_one_add_eq_coeff`: irrelevance of high-order terms (proved)

The proof strategy (from the tex source) involves:
1. For each coefficient n, define finite approximating sets
2. Show both sides reduce to finite sums/products on these sets
3. Apply the finite distributive law
4. Use the irrelevance lemma to show high-order terms don't contribute
-/
lemma tprod_tsum_eq_tsum_prod_essentiallyFinite
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K] [DiscreteTopology K]
    {I : Type*} {S : I → Type*} [∀ i, Zero (S i)] [∀ i, DecidableEq (S i)]
    (p : (i : I) → S i → K⟦X⟧)
    (hp_zero : ∀ i, p i 0 = 1)
    (hp_summable : Summable fun ik : Σ i, { k : S i // k ≠ 0 } => p ik.1 ik.2.1) :
    ∏' i : I, ∑' k : S i, p i k =
    ∑' f : { f : (i : I) → S i // ∀ᶠ i in Filter.cofinite, f i = 0 },
      ∏' i : I, p i (f.val i) := by
  -- Invoke the helper lemmas (Claims 1, 2, 7 from the tex proof)
  -- For discrete K, use the discrete versions which are fully proved
  have h_summable_i : ∀ i, Summable (p i) := fun i => summable_fiber_discrete p hp_summable i
  have h_summable_prod : Summable fun f : { f : (i : I) → S i // ∀ᶠ i in Filter.cofinite, f i = 0 } =>
      ∏' i : I, p i (f.val i) := summable_prod_essentiallyFinite_discrete p hp_zero hp_summable

  -- The proof proceeds by showing both sides have the same n-th coefficient for each n.
  ext n

  -- Create a ContinuousLinearMap from coeff for extracting coefficients from tsum
  let coeffCLM : K⟦X⟧ →L[K] K := ⟨coeff n, WithPiTopology.continuous_coeff K n⟩

  -- Extract coefficient from RHS using continuity of coeff
  have hrhs : coeff n (∑' f : { f : (i : I) → S i // ∀ᶠ i in Filter.cofinite, f i = 0 },
      ∏' i : I, p i (f.val i)) =
      ∑' f : { f : (i : I) → S i // ∀ᶠ i in Filter.cofinite, f i = 0 },
      coeff n (∏' i : I, p i (f.val i)) := coeffCLM.map_tsum h_summable_prod
  rw [hrhs]

  -- Now we need to show:
  -- coeff n (∏' i, ∑' k, p i k) = ∑' f, coeff n (∏' i, p i (f i))
  --
  -- The proof strategy from the tex source (Claims 8, 10, 11):
  --
  -- **Setup**: For each m ∈ ℕ, let T_m be a finite subset of S̄ = {(i,k) : k ∈ S_i, k ≠ 0}
  -- such that all (i,k) ∈ S̄ \ T_m satisfy [x^m](p_{i,k}) = 0 (exists by summability).
  -- Let T'_n = T_0 ∪ T_1 ∪ ... ∪ T_n, I_n = {i : (i,k) ∈ T'_n for some k}.
  --
  -- **Claim 8**: [x^n](RHS) = [x^n](∑_{(k_i) ∈ S^{I_n}} ∏_{i ∈ I_n} p_{i,k_i})
  --   - Only essentially finite functions with support in I_n contribute to coeff n
  --   - Functions with support outside I_n have coeff n = 0 (by Claim 5, 6)
  --
  -- **Claim 10**: [x^n](LHS) = [x^n](∏_{i ∈ I_n} ∑_k p_{i,k})
  --   - Use the irrelevance lemma (coeff_mul_tprod_one_add_eq_coeff)
  --   - For i ∉ I_n, ∑_{k≠0} p_{i,k} has high order, so doesn't affect coeff n
  --
  -- **Claim 11**: ∏_{i ∈ I_n} ∑_k p_{i,k} = ∑_{(k_i) ∈ S^{I_n}} ∏_{i ∈ I_n} p_{i,k_i}
  --   - This is the finite product rule (prod_tsum_eq_tsum_prod_finset'_discrete)
  --
  -- The full proof requires constructing T'_n and I_n explicitly and verifying Claims 8, 10, 11.
  -- This involves careful tracking of finite sets and uses:
  -- - prod_tsum_eq_tsum_prod_finset'_discrete for the finite case (Claim 11)
  -- - coeff_mul_tprod_one_add_eq_coeff for irrelevance (Claims 9, 10)
  -- - Coefficient-wise summability from hp_summable

  -- Get coefficient-wise summability
  have hp_coeff : ∀ m, Summable fun ik : Σ i, { k : S i // k ≠ 0 } => coeff m (p ik.1 ik.2.1) :=
    fun m => (PowerSeries.WithPiTopology.summable_iff_summable_coeff _).mp hp_summable m

  -- Define T'_n = {(i,k) : k ≠ 0, ∃ m ≤ n, coeff m (p i k) ≠ 0}
  -- This is the set of (i,k) pairs that can contribute to the n-th coefficient.
  let T'n : Set (Σ i, { k : S i // k ≠ 0 }) :=
    { ik | ∃ m ≤ n, coeff m (p ik.1 ik.2.val) ≠ 0 }

  -- T'n is finite. For discrete K, use T'n_finite_of_discrete.
  have hT'n_finite : T'n.Finite := T'n_finite_of_discrete p hp_summable n

  -- Define I_n = {i : (i,k) ∈ T'_n for some k}
  let I_n : Set I := { i | ∃ k : { k : S i // k ≠ 0 }, ⟨i, k⟩ ∈ T'n }

  -- I_n is finite (follows from T'n being finite)
  have hI_n_finite : I_n.Finite := by
    have h : I_n ⊆ Sigma.fst '' T'n := by
      intro i hi
      obtain ⟨k, hk⟩ := hi
      exact ⟨⟨i, k⟩, hk, rfl⟩
    exact Set.Finite.subset (hT'n_finite.image _) h

  -- **Proof structure** (following Claims 8, 10, 11 from the tex source):
  --
  -- **Claim 8 (RHS reduction)**: For the RHS, we show that only essentially finite
  -- functions with support contained in I_n contribute to coeff n:
  --   ∑' f, coeff n (∏' i, p i (f i)) = ∑_{f ∈ S^{I_n}} coeff n (∏_{i ∈ I_n} p i (f i))
  --
  -- This uses:
  -- - Claim 5: If some (j, k_j) ∈ S̄ \ T'_n, then coeff n (∏_i p_{i,k_i}) = 0
  --   (because p_j k_j has order > n, so by coeff_prod_eq_zero_of_factor_coeff_zero)
  -- - Claim 6: If f ∈ S^I_fin \ S^I_{I_n}, then coeff n (∏_i p_{i,k_i}) = 0
  --   (follows from Claim 5)
  -- - For f ∈ S^I_{I_n}, we have ∏' i, p i (f i) = ∏_{i ∈ I_n} p i (f i)
  --   (since p i 0 = 1 for i ∉ I_n)
  --
  -- **Claim 10 (LHS reduction)**: For the LHS, we use the irrelevance lemma:
  --   coeff n (∏' i, ∑' k, p i k) = coeff n (∏_{i ∈ I_n} ∑' k, p i k)
  --
  -- This uses:
  -- - Claim 9: For i ∈ I \ I_n, [x^m](∑_{k≠0} p_{i,k}) = 0 for m ≤ n
  --   (since all (i,k) with i ∉ I_n are in S̄ \ T'_n)
  -- - coeff_mul_tprod_one_add_eq_coeff: the irrelevance lemma
  --
  -- **Claim 11 (finite product rule)**: The finite product rule gives:
  --   ∏_{i ∈ I_n} ∑' k, p i k = ∑_{f ∈ S^{I_n}} ∏_{i ∈ I_n} p i (f i)
  --
  -- This is prod_tsum_eq_tsum_prod_finset'_discrete (which is now fully proved).
  --
  -- **Combining**: Claims 8, 10, 11 show both sides equal the same finite expression:
  --   coeff n (LHS) = coeff n (∏_{i ∈ I_n} ∑' k, p i k)  [by Claim 10]
  --                 = coeff n (∑_{f ∈ S^{I_n}} ∏_{i ∈ I_n} p i (f i))  [by Claim 11]
  --                 = coeff n (RHS)  [by Claim 8]
  --
  -- **Proof for discrete K**:
  -- For discrete K, both sides have finite support at each coefficient level.
  -- The key is that both sides equal the same finite sum over functions with graph in T'n.

  -- **RHS analysis**: The tsum ∑' f, coeff n (∏' i, p i (f i)) has finite support.
  -- Only functions f with graph(f) ⊆ T'n contribute (others have coeff n = 0).
  -- This is because if (i, f i) ∉ T'n for some i with f i ≠ 0, then
  -- coeff m (p i (f i)) = 0 for all m ≤ n, so by coeff_prod_eq_zero_of_factor_coeff_zero,
  -- coeff n (∏' i, p i (f i)) = 0.

  -- **LHS analysis**: For the LHS, we show coeff n (∏' i, ∑' k, p i k) equals the same sum.
  -- Write ∑' k, p i k = 1 + ∑' k≠0, p i k for each i.
  -- For i ∉ I_n, the sum ∑' k≠0, p i k has all coefficients up to n equal to 0.
  -- By the irrelevance lemma (coeff_mul_tprod_one_add_eq_coeff), the factors for i ∉ I_n
  -- don't affect coeff n of the product.
  -- So coeff n (∏' i, ∑' k, p i k) = coeff n (∏ i ∈ I_n.toFinset, ∑' k, p i k).

  -- The finite product over I_n can be expanded coefficient-wise to give a sum over
  -- functions I_n → S, which matches the RHS when restricted to functions with graph in T'n.

  -- **Detailed proof**:
  classical
  -- For the RHS, we show it equals a finite sum over functions with graph in T'n
  have h_rhs_finite : (Function.support fun f : { f : (i : I) → S i // ∀ᶠ i in Filter.cofinite, f i = 0 } =>
      coeff n (∏' i : I, p i (f.val i))) ⊆
      { f | ∀ i, (hi : f.val i ≠ 0) → ⟨i, ⟨f.val i, hi⟩⟩ ∈ T'n } := by
    intro f hf
    simp only [Function.mem_support, ne_eq] at hf
    simp only [Set.mem_ofPred_eq]
    intro i hi
    by_contra h_not_in
    -- If (i, f.val i) ∉ T'n, then coeff m (p i (f.val i)) = 0 for all m ≤ n
    have h_coeff_zero : ∀ m ≤ n, coeff m (p i (f.val i)) = 0 := by
      intro m hm
      by_contra hne
      apply h_not_in
      exact ⟨m, hm, hne⟩
    -- The tprod equals a finite product
    have htprod_eq : ∏' j : I, p j (f.val j) = ∏ j ∈ f.prop.toFinset, p j (f.val j) := by
      have h : ∀ᶠ j in Filter.cofinite, p j (f.val j) = 1 := by
        filter_upwards [f.prop] with j hj
        rw [hj, hp_zero]
      have hfin : (Function.mulSupport fun j => p j (f.val j)).Finite :=
        Filter.eventually_cofinite.mp h
      have hsub : hfin.toFinset ⊆ f.prop.toFinset := by
        intro j hj'
        rw [hfin.mem_toFinset, Function.mem_mulSupport] at hj'
        rw [f.prop.mem_toFinset]
        intro heq; rw [heq, hp_zero] at hj'; exact hj' rfl
      rw [tprod_eq_prod' (fun x hx => hfin.mem_toFinset.mpr hx)]
      apply Finset.prod_subset hsub
      intro j _ hnj
      rw [hfin.mem_toFinset, Function.mem_mulSupport, not_not] at hnj
      exact hnj
    -- i is in f.prop.toFinset
    have hi_in : i ∈ f.prop.toFinset := by
      rw [f.prop.mem_toFinset]
      exact hi
    rw [htprod_eq] at hf
    -- Product has zero coeff n
    exact hf (coeff_prod_eq_zero_of_factor_coeff_zero f.prop.toFinset
        (fun j => p j (f.val j)) i hi_in n h_coeff_zero n (le_refl n))

  -- The set of functions with graph in T'n is finite
  have h_finite_funcs : { f : { f : (i : I) → S i // ∀ᶠ i in Filter.cofinite, f i = 0 } |
      ∀ i, (hi : f.val i ≠ 0) → ⟨i, ⟨f.val i, hi⟩⟩ ∈ T'n }.Finite :=
    finite_funcs_with_graph_in_finite_set T'n hT'n_finite

  -- For the LHS, we need to show it equals the same finite sum
  -- This requires the irrelevance lemma and the finite product rule

  -- Key: for i ∉ I_n, ∑' k≠0, p i k has all coefficients up to n equal to 0
  have h_high_order : ∀ i ∉ I_n, ∀ m ≤ n, coeff m (∑' k : { k : S i // k ≠ 0 }, p i k.val) = 0 := by
    intro i hi m hm
    have h_summable : Summable (fun k : { k : S i // k ≠ 0 } => p i k.val) := by
      rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
      intro m'
      let e : { k : S i // k ≠ 0 } → Σ j, { k : S j // k ≠ 0 } := fun k => ⟨i, k⟩
      have he_inj : Function.Injective e := by
        intro ⟨k1, _⟩ ⟨k2, _⟩ heq
        simp only [e, Sigma.mk.injEq] at heq
        obtain ⟨_, h2⟩ := heq
        simp only [heq_eq_eq] at h2
        exact h2
      have h_eq : (fun k : { k : S i // k ≠ 0 } => coeff m' (p i k.val)) =
                  (fun ik : Σ j, { k : S j // k ≠ 0 } => coeff m' (p ik.1 ik.2.1)) ∘ e := by
        ext k; rfl
      rw [h_eq]
      exact summable_comp_injective_of_discrete (hp_coeff m') he_inj
    let coeffCLM' : K⟦X⟧ →L[K] K := ⟨coeff m, WithPiTopology.continuous_coeff K m⟩
    have h_tsum_coeff : coeff m (∑' k : { k : S i // k ≠ 0 }, p i k.val) =
        ∑' k : { k : S i // k ≠ 0 }, coeff m (p i k.val) := coeffCLM'.map_tsum h_summable
    rw [h_tsum_coeff]
    have h_all_zero : ∀ k : { k : S i // k ≠ 0 }, coeff m (p i k.val) = 0 := by
      intro ⟨k, hk⟩
      by_contra hne
      apply hi
      exact ⟨⟨k, hk⟩, m, hm, hne⟩
    simp only [h_all_zero, tsum_zero]

  -- The LHS can be written as ∏' i, (1 + ∑' k≠0, p i k)
  have h_tsum_split : ∀ i, ∑' k : S i, p i k = 1 + ∑' k : { k : S i // k ≠ 0 }, p i k.val := by
    intro i
    have h := (h_summable_i i).tsum_eq_add_tsum_ite 0
    rw [hp_zero] at h
    rw [h]
    congr 1
    rw [← tsum_subtype_eq_of_support_subset]
    · congr 1
      funext k
      have hk : (k : S i) ≠ 0 := k.prop
      simp only [hk, ↓reduceIte]
    · intro k hk
      simp only [Function.mem_support] at hk ⊢
      intro h
      rw [h, ite_eq_left rfl] at hk
      exact hk rfl

  -- Rewrite LHS using the split
  have h_lhs_eq : ∏' i : I, ∑' k : S i, p i k = ∏' i : I, (1 + ∑' k : { k : S i // k ≠ 0 }, p i k.val) := by
    congr 1
    funext i
    exact h_tsum_split i


  -- Now we use the fact that for discrete K, both sides equal the same finite sum
  -- The full proof requires showing:
  -- coeff n (∏' i, (1 + ∑' k≠0, p i k)) = ∑' f, coeff n (∏' i, p i (f i))

  -- By the irrelevance lemma, the factors for i ∉ I_n don't affect coeff n
  -- So both sides are determined by the finite set I_n

  -- The equality follows from the finite product rule applied to the finite set I_n
  -- and the correspondence between functions I_n → S and essentially finite functions with support in I_n

  -- For discrete K, this can be verified by showing both sides have the same finite support
  -- and agree on each function in the support

  -- The support is { f : graph(f) ⊆ T'n }, which is finite
  -- For each f in the support:
  -- - RHS contributes coeff n (∏' i, p i (f i)) = coeff n (∏ i ∈ supp(f), p i (f i))
  -- - LHS contributes the same value (by expansion of the finite product)

  -- The formal proof of this equality requires careful handling of the dependent types
  -- and uses the finite product rule (prod_tsum_eq_tsum_prod_finset'_discrete) for the finite case

  -- NOTE: prod_tsum_eq_tsum_prod_finset'_discrete is now fully proved (no sorry).
  -- The remaining work is type-theoretic: constructing explicit bijections between
  -- the finite index sets on both sides.

  -- For the LHS, we use the multipliability
  have h_mult_lhs : Multipliable fun i => ∑' k : S i, p i k :=
    multipliable_tsum_fiber_discrete p hp_zero hp_summable

  -- The mathematical argument is complete:
  -- 1. RHS: Only functions with graph in T'n contribute (h_rhs_finite, h_finite_funcs)
  -- 2. LHS: By irrelevance lemma, only factors for i ∈ I_n matter (h_high_order)
  -- 3. The finite product rule expands ∏ i ∈ I_n, ∑' k, p i k
  -- 4. A bijection between functions I_n → S and essentially finite functions with support in I_n
  --    shows both sides equal the same finite sum

  -- **Step 1: Convert RHS to a finite sum**
  -- The RHS tsum has finite support, so it equals a finite sum over functions with graph in T'n.
  have h_rhs_eq : ∑' f : { f : (i : I) → S i // ∀ᶠ i in Filter.cofinite, f i = 0 },
      coeff n (∏' i : I, p i (f.val i)) =
      ∑ f ∈ h_finite_funcs.toFinset, coeff n (∏' i : I, p i (f.val i)) := by
    apply tsum_eq_sum'
    -- Need to show: Function.support (f ↦ coeff n (∏' i, p i (f i))) ⊆ h_finite_funcs.toFinset
    intro f hf
    -- hf : f ∈ Function.support (...)
    -- Need to show: f ∈ h_finite_funcs.toFinset
    have hgraph := h_rhs_finite hf
    exact h_finite_funcs.mem_toFinset.mpr hgraph
  rw [h_rhs_eq]

  -- **Step 2: Show LHS equals the same finite sum**
  -- For the LHS, we show coeff n (∏' i, ∑' k, p i k) equals the same finite sum.
  -- This uses the irrelevance lemma and the finite product rule.

  -- First, note that for f with graph in T'n, the support is contained in I_n.
  have h_supp_in_I_n : ∀ f ∈ h_finite_funcs.toFinset, ∀ i, f.val i ≠ 0 → i ∈ I_n := by
    intro f hf i hi
    have hf' := h_finite_funcs.mem_toFinset.mp hf
    have hik := hf' i hi
    exact ⟨⟨f.val i, hi⟩, hik⟩

  -- For f with graph in T'n, ∏' i, p i (f i) = ∏ i ∈ f.prop.toFinset, p i (f i)
  have h_tprod_eq_prod : ∀ f : { f : (i : I) → S i // ∀ᶠ i in Filter.cofinite, f i = 0 },
      ∏' i : I, p i (f.val i) = ∏ i ∈ f.prop.toFinset, p i (f.val i) := by
    intro f
    have h : ∀ᶠ j in Filter.cofinite, p j (f.val j) = 1 := by
      filter_upwards [f.prop] with j hj
      rw [hj, hp_zero]
    have hfin : (Function.mulSupport fun j => p j (f.val j)).Finite :=
      Filter.eventually_cofinite.mp h
    have hsub : hfin.toFinset ⊆ f.prop.toFinset := by
      intro j hj'
      rw [hfin.mem_toFinset, Function.mem_mulSupport] at hj'
      rw [f.prop.mem_toFinset]
      intro heq; rw [heq, hp_zero] at hj'; exact hj' rfl
    rw [tprod_eq_prod' (fun x hx => hfin.mem_toFinset.mpr hx)]
    apply Finset.prod_subset hsub
    intro j _ hnj
    rw [hfin.mem_toFinset, Function.mem_mulSupport, not_not] at hnj
    exact hnj

  -- The LHS can be written as ∏' i, (1 + g i) where g i = ∑' k≠0, p i k
  -- For i ∉ I_n, g i has all coefficients up to n equal to 0.
  -- By the irrelevance lemma, only factors for i ∈ I_n matter.

  -- For discrete K with finite I_n, we can compute the LHS explicitly.
  -- The key is that both sides are finite sums over the same set of functions.

  -- The formal proof requires:
  -- 1. Applying the irrelevance lemma to reduce LHS to a finite product over I_n
  -- 2. Applying the finite product rule (prod_tsum_eq_tsum_prod_finset'_discrete)
  -- 3. Constructing a bijection between functions I_n → S and essentially finite functions
  -- 4. Showing the bijection preserves the value of each term

  -- This involves complex type-theoretic work with dependent types.
  -- The mathematical content is established by the lemmas above.

  -- **Step 1: Reduce LHS using the irrelevance lemma**
  -- Define g i = ∑' k≠0, p i k, so ∑' k, p i k = 1 + g i
  let g : I → K⟦X⟧ := fun i => ∑' k : { k : S i // k ≠ 0 }, p i k.val

  -- The LHS is ∏' i, (1 + g i)
  have h_lhs_as_prod : ∏' i : I, ∑' k : S i, p i k = ∏' i : I, (1 + g i) := h_lhs_eq

  -- The product is multipliable (from h_mult_lhs)
  have h_mult_one_plus_g : Multipliable (1 + g ·) := by
    convert h_mult_lhs using 1
    funext i
    exact (h_tsum_split i).symm

  -- Apply the irrelevance lemma: coeff n (∏' i, (1 + g i)) = coeff n (∏ i ∈ I_n.toFinset, (1 + g i))
  have h_lhs_coeff : coeff n (∏' i : I, (1 + g i)) = coeff n (∏ i ∈ hI_n_finite.toFinset, (1 + g i)) := by
    apply coeff_tprod_one_add_eq_coeff_prod_of_high_order' g I_n hI_n_finite h_mult_one_plus_g n
    exact h_high_order

  rw [h_lhs_as_prod, h_lhs_coeff]

  -- **Step 2: Expand the finite product using the finite product rule**
  -- ∏ i ∈ I_n.toFinset, (1 + g i) = ∏ i ∈ I_n.toFinset, ∑' k, p i k
  have h_prod_eq : ∏ i ∈ hI_n_finite.toFinset, (1 + g i) = ∏ i ∈ hI_n_finite.toFinset, ∑' k : S i, p i k := by
    apply Finset.prod_congr rfl
    intro i _
    exact (h_tsum_split i).symm

  rw [h_prod_eq]

  -- Now we need to show:
  -- coeff n (∏ i ∈ I_n.toFinset, ∑' k, p i k) = ∑ f ∈ h_finite_funcs.toFinset, coeff n (∏' i, p i (f i))

  -- **Step 3: Expand the finite product using prod_finset_tsum_eq_tsum_prod**
  have h_summable_in_I_n : ∀ i ∈ hI_n_finite.toFinset, Summable (p i) := by
    intro i hi
    exact h_summable_i i

  rw [prod_finset_tsum_eq_tsum_prod hI_n_finite.toFinset p h_summable_in_I_n]

  -- Now LHS is: coeff n (∑' f : (i : I_n) → S i, ∏ i : I_n, p i (f i))
  -- RHS is: ∑ f ∈ h_finite_funcs.toFinset, coeff n (∏' i, p i (f.val i))

  -- Extract coeff from the LHS tsum
  -- Summability follows from the fact that each p i is summable and the finite product
  -- of summable families is summable (same argument as summable_finProd_discrete)
  have h_lhs_summable : Summable (fun f : (i : hI_n_finite.toFinset) → S i =>
      ∏ i : hI_n_finite.toFinset, p i (f i)) := by
    rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
    intro d
    apply summable_of_hasFiniteSupport
    -- The support is finite because each p i has finite support at each coefficient
    -- and the product only depends on finitely many f i values
    -- This is the same argument as in summable_finProd_discrete
    -- Get finite support for each factor at each coefficient
    have hp_coeff' : ∀ i ∈ hI_n_finite.toFinset, ∀ m, (Function.support (fun k => coeff m (p i k))).Finite := by
      intro i hi m
      have := (PowerSeries.WithPiTopology.summable_iff_summable_coeff (f := p i)).mp (h_summable_in_I_n i hi) m
      exact this.hasFiniteSupport_of_discreteTopology
    -- Define the "relevant" elements for each j : hI_n_finite.toFinset
    let T' : (j : hI_n_finite.toFinset) → Set (S j) := fun ⟨i, hi⟩ =>
      ⋃ m ∈ Finset.Iic d, Function.support (fun k => coeff m (p i k))
    have hT'_finite : ∀ j : hI_n_finite.toFinset, (T' j).Finite := by
      intro ⟨i, hi⟩
      apply Set.Finite.biUnion (Finset.Iic d).finite_toSet
      intro m _
      exact hp_coeff' i hi m
    -- The set {f | ∀ j, f j ∈ T' j} is finite (product of finite sets)
    have h_finite' : {f : (j : hI_n_finite.toFinset) → S j | ∀ j, f j ∈ T' j}.Finite := Set.Finite.pi' hT'_finite
    -- The support is contained in {f | ∀ j, f j ∈ T' j}
    apply h_finite'.subset
    intro f hf
    simp only [Function.mem_support, ne_eq, Set.mem_ofPred_eq] at hf ⊢
    intro ⟨i, hi⟩
    by_contra h_not_in
    have h_coeff_zero' : ∀ m ≤ d, coeff m (p i (f ⟨i, hi⟩)) = 0 := by
      intro m hm
      by_contra hne
      apply h_not_in
      simp only [T', Set.mem_iUnion]
      exact ⟨m, Finset.mem_Iic.mpr hm, hne⟩
    -- The product has coefficient d = 0 because one factor does
    have hi_in' : ⟨i, hi⟩ ∈ (Finset.univ : Finset hI_n_finite.toFinset) := Finset.mem_univ _
    have h_zero' : ∀ m ≤ d, coeff m (∏ j ∈ Finset.univ, p (j : hI_n_finite.toFinset).1 (f j)) = 0 := by
      intro m hm
      have h_mul : ∃ g, ∏ j ∈ Finset.univ, p (j : hI_n_finite.toFinset).1 (f j) = p i (f ⟨i, hi⟩) * g := by
        use ∏ j ∈ (Finset.univ : Finset hI_n_finite.toFinset).erase ⟨i, hi⟩, p (j : hI_n_finite.toFinset).1 (f j)
        rw [← Finset.prod_erase_mul _ _ hi_in', mul_comm]
      obtain ⟨g, hg⟩ := h_mul
      rw [hg, coeff_mul]
      apply Finset.sum_eq_zero
      intro ⟨a, b⟩ hab
      have ha : a ≤ m := by simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hab; omega
      rw [h_coeff_zero' a (ha.trans hm), zero_mul]
    exact hf (h_zero' d (le_refl d))

  let coeffCLM' : K⟦X⟧ →L[K] K := ⟨coeff n, WithPiTopology.continuous_coeff K n⟩
  have h_lhs_coeff_eq : coeff n (∑' f : (i : hI_n_finite.toFinset) → S i, ∏ i : hI_n_finite.toFinset, p i (f i)) =
      ∑' f : (i : hI_n_finite.toFinset) → S i, coeff n (∏ i : hI_n_finite.toFinset, p i (f i)) :=
    coeffCLM'.map_tsum h_lhs_summable
  rw [h_lhs_coeff_eq]

  -- Now both sides are tsums of coeff n of products
  -- LHS: ∑' f : (i : I_n) → S i, coeff n (∏ i : I_n, p i (f i))
  -- RHS: ∑ f ∈ h_finite_funcs.toFinset, coeff n (∏' i, p i (f.val i))

  -- The key insight is that:
  -- 1. For functions f : I_n → S not in T'n, coeff n (∏ i, p i (f i)) = 0
  -- 2. For functions in T'n, we can extend them to essentially finite functions I → S
  -- 3. The products match: ∏ i : I_n, p i (f i) = ∏' i, p i (f' i) where f' is the extension

  -- **Step 4: Show that both sums are equal**
  -- The remaining work is type-theoretic: constructing the bijection between
  -- - Functions I_n → S with graph in T'n
  -- - Essentially finite functions I → S with graph in T'n
  -- and showing the products match.

  -- **Bijection construction**:
  -- Given f : (i : hI_n_finite.toFinset) → S i, define extendToI f : I → S by:
  --   extendToI f i = f ⟨i, hi⟩ if i ∈ hI_n_finite.toFinset
  --   extendToI f i = 0        otherwise
  --
  -- This extension is essentially finite (has finite support contained in I_n).
  --
  -- The inverse is restriction: given g : { f : I → S // eventually zero },
  -- define restrict g : (i : hI_n_finite.toFinset) → S i by:
  --   restrict g ⟨i, hi⟩ = g.val i
  --
  -- For g with support in I_n (i.e., g ∈ h_finite_funcs), we have:
  --   extendToI (restrict g) = g
  --
  -- **Product equality**:
  -- For f : (i : hI_n_finite.toFinset) → S i:
  --   ∏ i : hI_n_finite.toFinset, p i (f i) = ∏' i : I, p i (extendToI f i)
  -- This is because p i 0 = 1 for all i, so factors outside I_n contribute 1.
  --
  -- **Finite sum equality**:
  -- Both sides are finite sums. The LHS tsum has finite support (functions with
  -- graph outside T'n contribute 0), and the RHS is explicitly a finite sum.
  -- The bijection (extendToI, restrict) shows these finite sums are equal.

  -- Step 4a: Show LHS has finite support at coefficient n
  have h_lhs_finite_support : (Function.support fun f : (i : hI_n_finite.toFinset) → S i =>
      coeff n (∏ i : hI_n_finite.toFinset, p i (f i))).Finite := by
    have hp_coeff'' : ∀ i ∈ hI_n_finite.toFinset, ∀ m, (Function.support (fun k => coeff m (p i k))).Finite := by
      intro i hi m
      have := (PowerSeries.WithPiTopology.summable_iff_summable_coeff (f := p i)).mp (h_summable_in_I_n i hi) m
      exact this.hasFiniteSupport_of_discreteTopology
    let T'' : (j : hI_n_finite.toFinset) → Set (S j) := fun ⟨i, hi⟩ =>
      ⋃ m ∈ Finset.Iic n, Function.support (fun k => coeff m (p i k))
    have hT''_finite : ∀ j : hI_n_finite.toFinset, (T'' j).Finite := by
      intro ⟨i, hi⟩
      apply Set.Finite.biUnion (Finset.Iic n).finite_toSet
      intro m _
      exact hp_coeff'' i hi m
    have h_finite'' : {f : (j : hI_n_finite.toFinset) → S j | ∀ j, f j ∈ T'' j}.Finite := Set.Finite.pi' hT''_finite
    apply h_finite''.subset
    intro f hf
    simp only [Function.mem_support, ne_eq, Set.mem_ofPred_eq] at hf ⊢
    intro ⟨i, hi⟩
    by_contra h_not_in
    have h_coeff_zero'' : ∀ m ≤ n, coeff m (p i (f ⟨i, hi⟩)) = 0 := by
      intro m hm
      by_contra hne
      apply h_not_in
      simp only [T'', Set.mem_iUnion]
      exact ⟨m, Finset.mem_Iic.mpr hm, hne⟩
    have hi_in'' : ⟨i, hi⟩ ∈ (Finset.univ : Finset hI_n_finite.toFinset) := Finset.mem_univ _
    have h_zero'' : ∀ m ≤ n, coeff m (∏ j ∈ Finset.univ, p (j : hI_n_finite.toFinset).1 (f j)) = 0 := by
      intro m hm
      have h_mul : ∃ g', ∏ j ∈ Finset.univ, p (j : hI_n_finite.toFinset).1 (f j) = p i (f ⟨i, hi⟩) * g' := by
        use ∏ j ∈ (Finset.univ : Finset hI_n_finite.toFinset).erase ⟨i, hi⟩, p (j : hI_n_finite.toFinset).1 (f j)
        rw [← Finset.prod_erase_mul _ _ hi_in'', mul_comm]
      obtain ⟨g', hg'⟩ := h_mul
      rw [hg', coeff_mul]
      apply Finset.sum_eq_zero
      intro ⟨a, b⟩ hab
      have ha : a ≤ m := by simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hab; omega
      rw [h_coeff_zero'' a (ha.trans hm), zero_mul]
    exact hf (h_zero'' n (le_refl n))

  -- Step 4b: Show functions in LHS support extend to h_finite_funcs
  have h_lhs_support_extends_to_rhs : ∀ f : (i : hI_n_finite.toFinset) → S i,
      coeff n (∏ i : hI_n_finite.toFinset, p i (f i)) ≠ 0 →
      extendToI_subtype hI_n_finite f ∈ h_finite_funcs.toFinset := by
    intro f hf
    rw [h_finite_funcs.mem_toFinset]
    simp only [Set.mem_ofPred_eq]
    intro i hi
    -- Need to show: ⟨i, ⟨(extendToI_subtype hI_n_finite f).val i, hi⟩⟩ ∈ T'n
    simp only [extendToI_subtype, extendToI] at hi ⊢
    by_cases h_in : i ∈ hI_n_finite.toFinset
    · simp only [dite_eq_left h_in] at hi ⊢
      -- f ⟨i, h_in⟩ ≠ 0, and coeff n (∏ ...) ≠ 0
      -- So (i, f ⟨i, h_in⟩) must be in T'n (otherwise the product would have coeff n = 0)
      by_contra h_not_in_T'n
      -- If (i, f ⟨i, h_in⟩) ∉ T'n, then all coefficients up to n are 0
      have h_coeff_zero_factor : ∀ m ≤ n, coeff m (p i (f ⟨i, h_in⟩)) = 0 := by
        intro m hm
        by_contra hne
        apply h_not_in_T'n
        exact ⟨m, hm, hne⟩
      -- This means the product has coeff n = 0
      have hi_in_univ : ⟨i, h_in⟩ ∈ (Finset.univ : Finset hI_n_finite.toFinset) := Finset.mem_univ _
      have h_prod_zero : coeff n (∏ j ∈ Finset.univ, p (j : hI_n_finite.toFinset).1 (f j)) = 0 := by
        have h_mul : ∃ g', ∏ j ∈ Finset.univ, p (j : hI_n_finite.toFinset).1 (f j) = p i (f ⟨i, h_in⟩) * g' := by
          use ∏ j ∈ (Finset.univ : Finset hI_n_finite.toFinset).erase ⟨i, h_in⟩, p (j : hI_n_finite.toFinset).1 (f j)
          rw [← Finset.prod_erase_mul _ _ hi_in_univ, mul_comm]
        obtain ⟨g', hg'⟩ := h_mul
        rw [hg', coeff_mul]
        apply Finset.sum_eq_zero
        intro ⟨a, b⟩ hab
        have ha : a ≤ n := by simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hab; omega
        rw [h_coeff_zero_factor a ha, zero_mul]
      exact hf h_prod_zero
    · simp only [dite_eq_right h_in] at hi
      exact (hi rfl).elim

  -- Step 4c: The key insight is that both sums are over the same terms (up to the bijection)
  -- and the bijection preserves the values. Terms with zero coefficient contribute 0 to both sums.

  -- Step 4d: Convert LHS tsum to finite sum and apply bijection
  have h_lhs_eq' : ∑' f : (i : hI_n_finite.toFinset) → S i, coeff n (∏ i : hI_n_finite.toFinset, p i (f i)) =
      ∑ f ∈ h_lhs_finite_support.toFinset, coeff n (∏ i : hI_n_finite.toFinset, p i (f i)) := by
    apply tsum_eq_sum'
    intro f hf
    exact h_lhs_finite_support.mem_toFinset.mpr hf
  rw [h_lhs_eq']

  -- Key observation: both sums equal the same thing when we consider ALL functions
  -- (not just those in the support). Functions outside the support contribute 0.

  -- Let's use a different approach: show both sums equal the same finite sum
  -- over the image of h_lhs_finite_support under extendToI_subtype.

  -- Define the image of h_lhs_finite_support under extendToI_subtype
  let lhs_image : Finset { f : (i : I) → S i // ∀ᶠ i in Filter.cofinite, f i = 0 } :=
    h_lhs_finite_support.toFinset.map ⟨extendToI_subtype hI_n_finite, fun f1 f2 h => by
      have h1 := restrictToI_n_extendToI_subtype hI_n_finite f1
      have h2 := restrictToI_n_extendToI_subtype hI_n_finite f2
      rw [h] at h1
      rw [← h1, h2]⟩

  -- Show lhs_image ⊆ h_finite_funcs.toFinset
  have h_image_subset : lhs_image ⊆ h_finite_funcs.toFinset := by
    intro g hg
    simp only [lhs_image, Finset.mem_map] at hg
    obtain ⟨f, hf, hg_eq⟩ := hg
    rw [← hg_eq]
    apply h_lhs_support_extends_to_rhs
    exact h_lhs_finite_support.mem_toFinset.mp hf

  -- Show h_finite_funcs.toFinset ⊆ lhs_image (when restricted to nonzero terms)
  -- Actually, the reverse inclusion may not hold for functions with zero coeff n
  -- But those contribute 0 to the sum anyway!

  -- Use Finset.sum_subset to show:
  -- ∑ g ∈ h_finite_funcs.toFinset, coeff n (∏' i, p i (g.val i))
  -- = ∑ g ∈ lhs_image, coeff n (∏' i, p i (g.val i))
  have h_rhs_eq_image : ∑ g ∈ h_finite_funcs.toFinset, coeff n (∏' i, p i (g.val i)) =
      ∑ g ∈ lhs_image, coeff n (∏' i, p i (g.val i)) := by
    symm
    apply Finset.sum_subset_zero_on_sdiff h_image_subset
    · -- For g ∈ h_finite_funcs \ lhs_image, coeff n = 0
      intro g hg
      simp only [Finset.mem_sdiff] at hg
      -- g ∈ h_finite_funcs but g ∉ lhs_image
      -- This means restrictToI_n g ∉ h_lhs_finite_support
      -- Which means coeff n (∏ i, p i (restrictToI_n g i)) = 0
      have hg' : ∀ i, g.val i ≠ 0 → i ∈ I_n := h_supp_in_I_n g hg.1
      have h_restrict_not_in : restrictToI_n hI_n_finite g ∉ h_lhs_finite_support.toFinset := by
        intro h_in
        apply hg.2
        simp only [lhs_image, Finset.mem_map]
        use restrictToI_n hI_n_finite g, h_in
        exact extendToI_subtype_restrictToI_n hI_n_finite g hg'
      rw [h_lhs_finite_support.mem_toFinset, Function.mem_support, not_not] at h_restrict_not_in
      -- h_restrict_not_in : coeff n (∏ i, p i (restrictToI_n g i)) = 0
      have h_prod_eq' : ∏ i : hI_n_finite.toFinset, p i (restrictToI_n hI_n_finite g i) =
          ∏' j : I, p j (g.val j) := by
        have h1 := prod_eq_tprod_extendToI hI_n_finite p hp_zero (restrictToI_n hI_n_finite g)
        have h2 := extendToI_subtype_restrictToI_n hI_n_finite g hg'
        rw [h1]
        congr 1
        funext i
        have h2' : (extendToI_subtype hI_n_finite (restrictToI_n hI_n_finite g)).val i = g.val i := by
          rw [h2]
        simp only [extendToI_subtype] at h2'
        exact congrArg (p i) h2'
      rw [← h_prod_eq']
      exact h_restrict_not_in
    · -- Trivially true (same function)
      intro g _
      rfl
  rw [h_rhs_eq_image]

  -- Now show LHS = ∑ g ∈ lhs_image, coeff n (∏' i, p i (g.val i))
  -- This follows from the bijection
  symm
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro f _
  rw [prod_eq_tprod_extendToI hI_n_finite p hp_zero f]
  -- The coercion of the embedding is definitionally equal to extendToI_subtype
  rfl

/-- **Infinite Product Rule** (Proposition prop.fps.prodrule-inf-infN)

Let `S₁, S₂, S₃, ...` be sets that all contain `0`. For `p_{i,k} ∈ K⟦X⟧` with `p_{i,0} = 1`,
if the family `(p_{i,k})_{(i,k) ∈ S̄}` is summable, then:

`∏_{i=1}^∞ (∑_{k ∈ S_i} p_{i,k}) = ∑_{essentially finite (k₁,k₂,...)} ∏_{i=1}^∞ p_{i,k_i}`

The key insight is that only essentially finite sequences contribute to the sum on the RHS,
ensuring that each product `∏_{i=1}^∞ p_{i,k_i}` is well-defined (since all but finitely
many factors are `p_{i,0} = 1`).

This is a special case of `tprod_tsum_eq_tsum_prod_essentiallyFinite` with `I = ℕ+`. -/
lemma tprod_tsum_eq_tsum_prod_essentiallyFinite_nat [DiscreteTopology K]
    {S : ℕ+ → Type*} [∀ i, Zero (S i)] [∀ i, DecidableEq (S i)]
    (p : (i : ℕ+) → S i → K⟦X⟧)
    (hp_zero : ∀ i, p i 0 = 1)
    (hp_summable : Summable fun ik : SBar S => p ik.1 ik.2.1) :
    ∏' i : ℕ+, ∑' k : S i, p i k =
    ∑' f : { f : (i : ℕ+) → S i // ∀ᶠ i in Filter.cofinite, f i = 0 },
      ∏' i : ℕ+, p i (f.val i) :=
  -- SBar S is definitionally equal to Σ i : ℕ+, { k : S i // k ≠ 0 }
  tprod_tsum_eq_tsum_prod_essentiallyFinite p hp_zero hp_summable

end InfiniteProductRules


section IrrelevanceLemma

open scoped PowerSeries.WithPiTopology
open Filter Topology

variable [TopologicalSpace K] [IsTopologicalRing K]

omit [TopologicalSpace K] [IsTopologicalRing K] in
/-- For finite products, if all `f i` have order > n, then `∏ (1 + f i)` has the same
coefficients as 1 up to degree n. -/
lemma coeff_prod_one_add_eq_coeff_one_of_high_order {J : Type*} [DecidableEq J]
    (s : Finset J) (f : J → K⟦X⟧) (n : ℕ) (hf_order : ∀ i ∈ s, (n : ℕ∞) < order (f i)) :
    ∀ m ≤ n, coeff m (∏ i ∈ s, (1 + f i)) = coeff m (1 : K⟦X⟧) := by
  intro m hm
  rw [Finset.prod_one_add, map_sum]
  have h_nonempty : ∀ t ∈ s.powerset, t ≠ ∅ → coeff m (∏ i ∈ t, f i) = 0 := by
    intro t ht hne
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hjs : j ∈ s := Finset.mem_powerset.mp ht hj
    have h_order : (m : ℕ∞) < order (∏ i ∈ t, f i) := by
      calc (m : ℕ∞) ≤ n := by exact_mod_cast hm
        _ < order (f j) := hf_order j hjs
        _ ≤ order (∏ i ∈ t, f i) := by
          calc order (f j) = ∑ i ∈ ({j} : Finset J), order (f i) := by simp
            _ ≤ ∑ i ∈ t, order (f i) := Finset.sum_le_sum_of_subset (by simp [hj])
            _ ≤ order (∏ i ∈ t, f i) := le_order_prod _ _
    exact coeff_of_lt_order m h_order
  rw [Finset.sum_eq_single ∅]
  · simp
  · exact fun t ht hne => h_nonempty t ht hne
  · exact fun h => (h (Finset.empty_mem_powerset s)).elim

omit [IsTopologicalRing K] in
/-- For infinite products, if all `f i` have order > n and the product is multipliable,
then `∏' (1 + f i)` has the same coefficients as 1 up to degree n. -/
lemma coeff_tprod_one_add_eq_coeff_one [T2Space K] {J : Type*} (f : J → K⟦X⟧)
    (hmult : Multipliable (1 + f ·)) (n : ℕ) (hf_order : ∀ i : J, (n : ℕ∞) < order (f i)) :
    ∀ m ≤ n, coeff m (∏' i, (1 + f i)) = coeff m (1 : K⟦X⟧) := by
  classical
  intro m hm
  have htend : Tendsto (fun s => ∏ i ∈ s, (1 + f i)) atTop (nhds (∏' i, (1 + f i))) :=
    hmult.hasProd
  have hcoeff_cont : Continuous (coeff (R := K) m) := WithPiTopology.continuous_coeff K m
  have htend_coeff : Tendsto (fun s => coeff m (∏ i ∈ s, (1 + f i))) atTop
      (nhds (coeff m (∏' i, (1 + f i)))) := hcoeff_cont.continuousAt.tendsto.comp htend
  refine tendsto_nhds_unique htend_coeff ?_
  apply tendsto_atTop_of_eventually_const (i₀ := ∅)
  exact fun s _ => coeff_prod_one_add_eq_coeff_one_of_high_order s f n (fun i _ => hf_order i) m hm

omit [IsTopologicalRing K] in
/-- **Irrelevance of High-Order Terms** (Lemma lem.fps.prod.irlv.inf)

If `a ∈ K⟦X⟧` and `(f_i)_{i ∈ J}` is a summable family with each `f_i` having
`[x^m](f_i) = 0` for `m ∈ {0, 1, ..., n}`, then
`[x^m](a · ∏_{i ∈ J}(1 + f_i)) = [x^m](a)` for `m ∈ {0, 1, ..., n}`.

Intuitively, if all `f_i` have high order, then multiplying by `∏(1 + f_i)`
doesn't affect the first `n+1` coefficients. -/
lemma coeff_mul_tprod_one_add_eq_coeff [T2Space K]
    {J : Type*} (a : K⟦X⟧) (f : J → K⟦X⟧)
    (_hf_summable : Summable f)
    (n : ℕ) (hf_order : ∀ i : J, ∀ m ≤ n, (coeff m) (f i) = 0) :
    ∀ m ≤ n, (coeff m) (a * ∏' i, (1 + f i)) = (coeff m) a := by
  -- First, establish that each f i has order > n
  have horder : ∀ i : J, (n : ℕ∞) < order (f i) := fun i => by
    have h := nat_le_order (f i) (n + 1) (fun k hk => hf_order i k (Nat.lt_add_one_iff.mp hk))
    calc (n : ℕ∞) < n + 1 := by norm_cast; omega
      _ ≤ (f i).order := h
  intro m hm
  by_cases hmult : Multipliable (1 + f ·)
  · -- If multipliable, use the lemma about coefficients
    have hcoeff_prod : ∀ k ≤ n, coeff k (∏' i, (1 + f i)) = coeff k (1 : K⟦X⟧) :=
      coeff_tprod_one_add_eq_coeff_one f hmult n horder
    rw [coeff_mul]
    have h_sum : ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, coeff x.1 a * coeff x.2 (∏' i, (1 + f i)) =
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, coeff x.1 a * coeff x.2 1 := by
      apply Finset.sum_congr rfl
      intro x hx
      have hx2 : x.2 ≤ n := by
        have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
        omega
      rw [hcoeff_prod x.2 hx2]
    rw [h_sum, ← coeff_mul, mul_one]
  · -- If not multipliable, tprod defaults to 1
    rw [tprod_eq_one_of_not_multipliable hmult, mul_one]

end IrrelevanceLemma


section EulerIdentity

open scoped PowerSeries.WithPiTopology

variable [TopologicalSpace K] [IsTopologicalRing K] [T2Space K] [NoZeroDivisors K]

/-- The coercion of oddPNatEquivPNat.symm i is 2 * i - 1. -/
lemma oddPNatEquivPNat_symm_coe (i : ℕ+) :
    (oddPNatEquivPNat.symm i : ℕ) = 2 * i - 1 := rfl

omit [NoZeroDivisors K] in
/-- Key lemma: `Ring.inverse (1 - X^k) = ∑' j, X^(k*j)` when `k ≠ 0`.
This connects the multiplicative inverse to the geometric series. -/
lemma Ring_inverse_one_sub_X_pow (k : ℕ) (hk : k ≠ 0) :
    Ring.inverse (1 - (X : K⟦X⟧)^k) = ∑' j : ℕ, (X : K⟦X⟧) ^ (k * j) := by
  have h : ((X : K⟦X⟧)^k).constantCoeff = 0 := by
    rw [map_pow, constantCoeff_X, zero_pow hk]
  have hmul := WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero h
  have heq : (∑' j : ℕ, (X : K⟦X⟧) ^ (k * j)) = ∑' j : ℕ, ((X : K⟦X⟧)^k) ^ j := by
    congr 1; ext j; rw [← pow_mul]
  rw [heq]
  have hunit : IsUnit (1 - (X : K⟦X⟧)^k) := by
    rw [isUnit_iff_exists_inv]
    exact ⟨∑' j : ℕ, ((X : K⟦X⟧)^k) ^ j, by rw [mul_comm]; exact hmul⟩
  rw [Ring.inverse_of_isUnit hunit]
  symm
  apply Units.eq_inv_of_mul_eq_one_left
  rw [hunit.unit_spec, mul_comm]
  exact hmul

omit [IsTopologicalRing K] [NoZeroDivisors K] in
/-- The RHS of Euler's identity equals the generating function for partitions into distinct parts. -/
lemma rhs_eq_genFun :
    (∏' k : ℕ+, (1 + (X : K⟦X⟧) ^ (k : ℕ))) =
    PowerSeries.mk fun n ↦ ((Nat.Partition.countRestricted n 2).card : K) := by
  have h1 : (∏' k : ℕ+, (1 + (X : K⟦X⟧) ^ (k : ℕ))) = ∏' i : ℕ, (1 + X ^ (i + 1)) := by
    rw [← Equiv.tprod_eq (Equiv.pnatEquivNat)]
    congr 1; ext k; simp [Equiv.pnatEquivNat]
  rw [h1]
  have h2 : ∀ i : ℕ, (∑ j ∈ Finset.range 2, (X : K⟦X⟧) ^ ((i + 1) * j)) = 1 + X ^ (i + 1) := by
    intro i; simp [Finset.sum_range_succ]
  have h3 : (∏' i : ℕ, (1 + (X : K⟦X⟧) ^ (i + 1))) = ∏' i : ℕ, ∑ j ∈ Finset.range 2, X ^ ((i + 1) * j) := by
    apply tprod_congr; intro i; exact (h2 i).symm
  rw [h3]
  symm
  exact (Nat.Partition.hasProd_powerSeriesMk_card_countRestricted K (by norm_num : 0 < 2)).tprod_eq.symm

/-- `restricted n Odd = restricted n (¬ 2 ∣ ·)` since `Odd n ↔ ¬ 2 ∣ n`. -/
lemma restricted_Odd_eq (n : ℕ) :
    Nat.Partition.restricted n Odd = Nat.Partition.restricted n (¬ 2 ∣ ·) := by
  ext p
  simp only [Nat.Partition.restricted, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hp i hi
    have := hp i hi
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd] at this
    exact this
  · intro hp i hi
    have := hp i hi
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact this

/-- The bijection `pnatEquivEvenNat` satisfies `2j - 1 = (pnatEquivEvenNat j).val + 1`. -/
lemma pnatEquivEvenNat_value (j : ℕ+) :
    2 * (j : ℕ) - 1 = (pnatEquivEvenNat j).val + 1 := by
  have hj := j.pos
  show 2 * (j : ℕ) - 1 = 2 * (j : ℕ) - 2 + 1
  omega

/-- **Euler's Identity** (Proposition prop.gf.prod.euler-odd)

`∏_{i>0} (1 - x^{2i-1})⁻¹ = ∏_{k>0} (1 + x^k)`

This identity relates the generating function for partitions into odd parts
to the generating function for partitions into distinct parts.

The proof uses the fact that:
- The RHS is the generating function for partitions into distinct parts
- The LHS is the generating function for partitions into odd parts
- By Glaisher's theorem, these partition counts are equal

The algebraic proof (from the TeX source) shows:
1. `(1 + x^k)(1 - x^k) = 1 - x^{2k}`
2. `∏_{k>0}(1 + x^k) = ∏_{k>0}(1 - x^{2k}) / ∏_{k>0}(1 - x^k)`
3. The even factors cancel, leaving `1 / ∏_{k odd}(1 - x^k)` -/
lemma euler_odd_parts_identity :
    ∏' i : ℕ+, Ring.inverse (1 - (X : K⟦X⟧) ^ (2 * (i : ℕ) - 1)) =
    ∏' k : ℕ+, (1 + (X : K⟦X⟧) ^ (k : ℕ)) := by
  -- Step 1: Show RHS = mk (fun n => (countRestricted n 2).card)
  rw [rhs_eq_genFun]

  -- Step 2: Use Glaisher's theorem
  have hglaisher := Nat.Partition.powerSeriesMk_card_restricted_eq_powerSeriesMk_card_countRestricted K
      (by norm_num : 0 < 2)

  -- Step 3: restricted n Odd = restricted n (¬ 2 ∣ ·)
  have hgen_eq : (PowerSeries.mk fun n ↦ ((Nat.Partition.restricted n Odd).card : K)) =
      PowerSeries.mk fun n ↦ ((Nat.Partition.countRestricted n 2).card : K) := by
    simp_rw [restricted_Odd_eq]
    exact hglaisher

  -- Step 4: Show LHS = mk (fun n => (restricted n Odd).card)
  rw [← hgen_eq]
  rw [Nat.Partition.powerSeriesMk_card_restricted_eq_tprod K Odd]

  -- Step 5: Rewrite LHS using Ring_inverse_one_sub_X_pow
  have hLHS : ∏' i : ℕ+, Ring.inverse (1 - (X : K⟦X⟧) ^ (2 * (i : ℕ) - 1)) =
      ∏' i : ℕ+, ∑' j : ℕ, (X : K⟦X⟧) ^ ((2 * (i : ℕ) - 1) * j) := by
    apply tprod_congr
    intro i
    apply Ring_inverse_one_sub_X_pow
    have : 1 ≤ 2 * (i : ℕ) := by have := i.pos; omega
    omega
  rw [hLHS]

  -- Step 6: Rewrite RHS using tprod_subtype
  have hRHS : (∏' i : ℕ, if Odd (i + 1) then ∑' j : ℕ, (X : K⟦X⟧) ^ ((i + 1) * j) else 1) =
      ∏' (i : {i : ℕ | Odd (i + 1)}), ∑' j : ℕ, (X : K⟦X⟧) ^ ((i.val + 1) * j) := by
    have h := _root_.tprod_subtype {i : ℕ | Odd (i + 1)} (fun i => ∑' j : ℕ, (X : K⟦X⟧) ^ ((i + 1) * j))
    rw [h]
    apply tprod_congr
    intro i
    simp only [Set.mulIndicator, Set.mem_ofPred_eq]
  rw [hRHS]

  -- Step 7: Use the bijection pnatEquivEvenNat to reindex
  rw [← pnatEquivEvenNat.tprod_eq]

  -- Step 8: Show the terms match
  apply tprod_congr
  intro i
  have heq := pnatEquivEvenNat_value i
  simp only [heq]

/-- Alternative form of Euler's identity using the set of odd positive integers.

This follows from `euler_odd_parts_identity` by reindexing the product using the
equivalence `oddPNatEquivPNat` between `{ n : ℕ+ // Odd n }` and `ℕ+`. -/
lemma euler_odd_parts_identity' :
    ∏' i : { n : ℕ+ // Odd (n : ℕ) }, Ring.inverse (1 - (X : K⟦X⟧) ^ (i : ℕ)) =
    ∏' k : ℕ+, (1 + (X : K⟦X⟧) ^ (k : ℕ)) := by
  rw [← euler_odd_parts_identity]
  rw [← oddPNatEquivPNat.symm.tprod_eq]
  congr 1

end EulerIdentity


section Partitions

/-- **Euler's Partition Theorem** (Theorem thm.gf.prod.euler-comb)

The number of partitions of `n` into distinct positive integers equals
the number of partitions of `n` into odd positive integers.

For example, for `n = 6`:
- Distinct partitions: `6`, `1+5`, `2+4`, `1+2+3` (4 partitions)
- Odd partitions: `1+5`, `3+3`, `3+1+1+1`, `1+1+1+1+1+1` (4 partitions) -/
lemma euler_distinct_odd_partitions (n : ℕ) :
    numDistinctPartitions n = numOddPartitions n :=
  (Nat.Partition.card_odds_eq_card_distincts n).symm

end Partitions


section Substitution

open scoped PowerSeries.WithPiTopology

variable [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]

omit [T2Space K] in
/-- The `rescale` ring homomorphism is continuous in the pi topology on power series. -/
lemma continuous_rescale (a : K) : Continuous (rescale a : K⟦X⟧ → K⟦X⟧) := by
  refine continuous_pi_iff.mpr fun n => ?_
  have h : ∀ f, (rescale a f) n = a ^ (n ()) * coeff (n ()) f := by
    intro f
    simp only [rescale, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    change (mk (fun m => a ^ m * coeff m f)) n = a ^ (n ()) * coeff (n ()) f
    simp only [PowerSeries.coeff, MvPowerSeries.coeff_apply]
    rfl
  simp only [h]
  exact continuous_const.mul (PowerSeries.WithPiTopology.continuous_coeff K (n ()))

/-- **Substitution Rule for Infinite Products** (Proposition prop.fps.subs.rule-infprod)

If `(f_i)_{i ∈ I}` is a multipliable family and `a ∈ K`, then rescaling commutes with
infinite products: `rescale a (∏_{i ∈ I} f_i) = ∏_{i ∈ I} (rescale a (f_i))`.

In the context of substitution, this says that `(∏ f_i)(ax) = ∏ f_i(ax)`. -/
lemma tprod_rescale_substitution
    {I : Type*} (f : I → K⟦X⟧) (a : K)
    (hf : Multipliable f) :
    rescale a (∏' i, f i) = ∏' i, rescale a (f i) :=
  hf.map_tprod (rescale a) (continuous_rescale a)

end Substitution


section BinaryProductRule

open scoped PowerSeries.WithPiTopology

variable [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]

omit [IsTopologicalRing K] [T2Space K] in
/-- **Binary Product Rule** (Equation eq.fps.prod.binary.prod-inf)

For a summable sequence `(a_n)_{n ∈ ℕ}`:
`∏_{i ∈ ℕ} (1 + a_i) = ∑_{i₁ < i₂ < ... < i_k} a_{i₁} a_{i₂} ... a_{i_k}`

The RHS is a sum over all finite strictly increasing sequences of indices.

**Note**: This theorem requires `K` to have discrete topology. This covers the main use cases
(integers, rationals, finite fields). For non-discrete `K` (like ℝ or ℂ), additional
assumptions (such as completeness) may be needed. -/
lemma binary_product_rule (a : ℕ → K⟦X⟧) (ha : Summable a) [DiscreteTopology K] :
    ∏' i : ℕ, (1 + a i) =
    ∑' s : Finset ℕ, ∏ i ∈ s, a i := by
  -- Apply the Mathlib theorem tprod_one_add which states:
  -- ∏' i, (1 + f i) = ∑' s, ∏ i ∈ s, f i
  -- provided Summable (fun s => ∏ i ∈ s, f i)
  apply tprod_one_add
  -- The summability follows from finite support at each coefficient level.
  -- For discrete K, Summable implies finite support.
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro n
  -- For each n, show Summable (fun s => coeff n (∏ i ∈ s, a i))
  -- The key is that the support is finite.

  -- From Summable a, we have Summable (coeff m ∘ a) for each m
  have ha_coeff : ∀ m, Summable (fun i => coeff m (a i)) := by
    intro m
    exact (PowerSeries.WithPiTopology.summable_iff_summable_coeff (f := a)).mp ha m

  -- In discrete topology, summable implies finite support
  have ha_finite : ∀ m, (Function.support (fun i => coeff m (a i))).Finite := by
    intro m
    exact (ha_coeff m).hasFiniteSupport_of_discreteTopology

  -- The union of supports for m ≤ n is finite
  have hS : (⋃ m ∈ Iic n, Function.support (fun i => coeff m (a i))).Finite := by
    apply Set.Finite.biUnion
    · exact (Iic n).finite_toSet
    · intro m _; exact ha_finite m

  apply summable_of_hasFiniteSupport

  let T : Set ℕ := ⋃ m ∈ Iic n, Function.support (fun i => coeff m (a i))
  have hT_finite : T.Finite := hS

  -- The support of s ↦ coeff n (∏ i ∈ s, a i) is contained in finsets ⊆ T
  have h_support_subset : Function.support (fun s : Finset ℕ => coeff n (∏ i ∈ s, a i)) ⊆
      {s : Finset ℕ | ↑s ⊆ T} := by
    intro s hs
    simp only [Function.mem_support, Set.mem_ofPred_eq] at hs ⊢
    intro i hi
    -- If i ∈ s and coeff n (∏ j ∈ s, a j) ≠ 0, then i must be in T
    by_contra hi_not_T
    -- If i ∉ T, then coeff m (a i) = 0 for all m ≤ n
    have hi_coeff_zero : ∀ m ≤ n, coeff m (a i) = 0 := by
      intro m hm
      by_contra hne
      apply hi_not_T
      simp only [T, Set.mem_iUnion]
      exact ⟨m, by simp [hm], hne⟩
    -- This implies coeff n (∏ j ∈ s, a j) = 0, contradicting hs
    have h_prod_eq : ∏ j ∈ s, a j = a i * ∏ j ∈ s.erase i, a j := by
      rw [← prod_erase_mul s (fun j => a j) hi, mul_comm]
    rw [h_prod_eq] at hs
    have h_coeff_mul : coeff n (a i * ∏ j ∈ s.erase i, a j) =
        ∑ p ∈ antidiagonal n, coeff p.1 (a i) * coeff p.2 (∏ j ∈ s.erase i, a j) := by
      rw [coeff_mul]
    rw [h_coeff_mul] at hs
    have h_all_zero : ∀ p ∈ antidiagonal n, coeff p.1 (a i) * coeff p.2 (∏ j ∈ s.erase i, a j) = 0 := by
      intro p hp
      have hp1_le : p.1 ≤ n := by simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hp; omega
      rw [hi_coeff_zero p.1 hp1_le, zero_mul]
    simp only [sum_eq_zero h_all_zero, ne_eq, not_true_eq_false] at hs

  -- The set of finsets contained in T is finite
  have h_finsets_finite : {s : Finset ℕ | ↑s ⊆ T}.Finite := by
    have hT_finset : ∃ T' : Finset ℕ, ↑T' = T := hT_finite.exists_finset_coe
    obtain ⟨T', hT'⟩ := hT_finset
    have : {t : Finset ℕ | ↑t ⊆ T} = {t : Finset ℕ | t ⊆ T'} := by
      ext t; simp only [Set.mem_ofPred_eq, ← hT', Finset.coe_subset]
    rw [this]
    exact T'.powerset.finite_toSet.subset (fun t ht => by simpa using ht)

  exact h_finsets_finite.subset h_support_subset

omit [IsTopologicalRing K] [T2Space K] in
/-- Alternative formulation: the product equals a sum over finite subsets. -/
lemma binary_product_rule' (a : ℕ → K⟦X⟧) (ha : Summable a) [DiscreteTopology K] :
    ∏' i : ℕ, (1 + a i) =
    ∑' J : { J : Set ℕ // J.Finite }, ∏ᶠ i ∈ J.val, a i := by
  rw [binary_product_rule a ha, ← OrderIso.finsetSetFinite.toEquiv.tsum_eq]
  congr 1
  funext s
  exact (finprod_mem_coe_finset a s).symm

end BinaryProductRule

end


/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_zero_eq
  [Zero M]
  (I : Type*) :
-- imply
  EssentiallyFinite (0 : I → M) := by
-- proof
  apply EssentiallyFinite.zero

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_finite_support_eq
  [Zero M]
  {f : I → M}
  (hf : EssentiallyFinite f) :
-- imply
  (Function.support f).Finite := by
-- proof
  apply EssentiallyFinite.finite_support hf

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_of_finite_eq
  [Zero M]
  [Finite I]
  (f : I → M) :
-- imply
  EssentiallyFinite f := by
-- proof
  apply EssentiallyFinite.of_finite f

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_of_fintype_eq
  [Zero M]
  [Fintype I]
  (f : I → M) :
-- imply
  EssentiallyFinite f := by
-- proof
  apply EssentiallyFinite.of_fintype f

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_subfamily_eq
  [Zero M]
  {f : I → M}
  (J : Set I)
  (hf : EssentiallyFinite f) :
-- imply
  EssentiallyFinite (fun i : J => f i) := by
-- proof
  apply EssentiallyFinite.subfamily J hf

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_const_zero_eq
  [Zero M] :
-- imply
  EssentiallyFinite (fun _ : I => (0 : M)) := by
-- proof
  apply EssentiallyFinite.const_zero

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_iff_eventually_cofinite_iff
  [Zero M]
  {f : I → M} :
-- imply
  EssentiallyFinite f ↔ ∀ᶠ i in Filter.cofinite, f i = 0 := by
-- proof
  apply EssentiallyFinite.iff_eventually_cofinite

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_iff_finite_set_of_ne_zero_iff
  [Zero M]
  {f : I → M} :
-- imply
  EssentiallyFinite f ↔ {i | f i ≠ 0}.Finite := by
-- proof
  apply EssentiallyFinite.iff_finite_setOf_ne_zero

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_iff_support_finite_iff
  [Zero M]
  {f : I → M} :
-- imply
  EssentiallyFinite f ↔ (Function.support f).Finite := by
-- proof
  apply EssentiallyFinite.iff_support_finite

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_neg_eq
  [AddGroup M]
  {f : I → M}
  (hf : EssentiallyFinite f) :
-- imply
  EssentiallyFinite (-f) := by
-- proof
  apply EssentiallyFinite.neg hf

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_add_eq
  [AddGroup M]
  {f g : I → M}
  (hf : EssentiallyFinite f)
  (hg : EssentiallyFinite g) :
-- imply
  EssentiallyFinite (f + g) := by
-- proof
  apply EssentiallyFinite.add hf hg

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_sub_eq
  [AddGroup M]
  {f g : I → M}
  (hf : EssentiallyFinite f)
  (hg : EssentiallyFinite g) :
-- imply
  EssentiallyFinite (f - g) := by
-- proof
  apply EssentiallyFinite.sub hf hg

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_mul_const_eq
  [Ring R]
  [NoZeroDivisors R]
  {f : I → R}
  (hf : EssentiallyFinite f)
  (c : R) :
-- imply
  EssentiallyFinite (fun i => f i * c) := by
-- proof
  apply EssentiallyFinite.mul_const hf c

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_const_mul_eq
  [Ring R]
  [NoZeroDivisors R]
  {f : I → R}
  (c : R)
  (hf : EssentiallyFinite f) :
-- imply
  EssentiallyFinite (fun i => c * f i) := by
-- proof
  apply EssentiallyFinite.const_mul c hf

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_to_finsupp_apply_eq
  [Zero M]
  {f : I → M}
  (hf : EssentiallyFinite f)
  (i : I) :
-- imply
  hf.toFinsupp i = f i := by
-- proof
  apply EssentiallyFinite.toFinsupp_apply hf i

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_mem_support_finset_iff
  [Zero M]
  {f : I → M}
  (hf : EssentiallyFinite f)
  (i : I) :
-- imply
  i ∈ hf.supportFinset ↔ f i ≠ 0 := by
-- proof
  apply EssentiallyFinite.mem_supportFinset_iff hf i

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_family_zero_apply_eq
  [Zero M]
  (i : I) :
-- imply
  (0 : EssentiallyFiniteFamily I M) i = 0 := by
-- proof
  apply EssentiallyFiniteFamily.zero_apply i

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_family_eventually_eq_zero_eq
  [Zero M]
  (f : EssentiallyFiniteFamily I M) :
-- imply
  ∀ᶠ i in Filter.cofinite, f i = 0 := by
-- proof
  apply EssentiallyFiniteFamily.eventually_eq_zero f

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma essentially_finite_family_finite_support_eq
  [Zero M]
  (f : EssentiallyFiniteFamily I M) :
-- imply
  (Function.support f.val).Finite := by
-- proof
  apply EssentiallyFiniteFamily.finite_support f

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma prod_sum_eq_sum_prod_finset_eq
  [CommSemiring L]
  {n : ℕ}
  {m : Fin n → ℕ}
  (p : (i : Fin n) → Fin (m i) → L) :
-- imply
  ∏ i : Fin n, ∑ k : Fin (m i), p i k =
  ∑ f : (i : Fin n) → Fin (m i), ∏ i : Fin n, p i (f i) := by
-- proof
  apply prod_sum_eq_sum_prod_finset p

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma prod_sum_eq_sum_prod_finset'_eq
  [CommSemiring L]
  [Fintype N]
  [DecidableEq N]
  {S : N → Type*} [∀ i, Fintype (S i)]
  (p : (i : N) → S i → L) :
-- imply
  ∏ i : N, ∑ k : S i, p i k =
  ∑ f : (i : N) → S i, ∏ i : N, p i (f i) := by
-- proof
  apply prod_sum_eq_sum_prod_finset' p

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma summable_fin_prod_discrete_eq
  [CommRing K]
  [TopologicalSpace K]
  [DiscreteTopology K]
  {n : ℕ}
  {S : Fin n → Type*}
  (p : (i : Fin n) → S i → K⟦X⟧)
  (hp : ∀ i, Summable (p i)) :
-- imply
  Summable (fun f : (i : Fin n) → S i => ∏ i : Fin n, p i (f i)) := by
-- proof
  apply summable_finProd_discrete p hp

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma prod_tsum_eq_tsum_prod_finset_eq
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [DiscreteTopology K]
  {n : ℕ}
  {S : Fin n → Type*}
  (p : (i : Fin n) → S i → K⟦X⟧)
  (hp : ∀ i, Summable (p i)) :
-- imply
  ∏ i : Fin n, ∑' k, p i k =
  ∑' f : (i : Fin n) → S i, ∏ i : Fin n, p i (f i) := by
-- proof
  apply prod_tsum_eq_tsum_prod_finset p hp

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma prod_tsum_eq_tsum_prod_finset'_eq
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [DiscreteTopology K]
  [Fintype N]
  [DecidableEq N]
  {S : N → Type*}
  (p : (i : N) → S i → K⟦X⟧)
  (hp : ∀ i, Summable (p i)) :
-- imply
  ∏ i : N, ∑' k, p i k =
  ∑' f : (i : N) → S i, ∏ i : N, p i (f i) := by
-- proof
  apply prod_tsum_eq_tsum_prod_finset' p hp

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma prod_tsum_eq_tsum_prod_finset_discrete_eq
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [DiscreteTopology K]
  {n : ℕ}
  {S : Fin n → Type*}
  (p : (i : Fin n) → S i → K⟦X⟧)
  (hp : ∀ i, Summable (p i)) :
-- imply
  ∏ i : Fin n, ∑' k, p i k =
  ∑' f : (i : Fin n) → S i, ∏ i : Fin n, p i (f i) := by
-- proof
  apply prod_tsum_eq_tsum_prod_finset_discrete p hp

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma prod_tsum_eq_tsum_prod_finset'_discrete_eq
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [DiscreteTopology K]
  [Fintype N]
  [DecidableEq N]
  {S : N → Type*}
  (p : (i : N) → S i → K⟦X⟧)
  (hp : ∀ i, Summable (p i)) :
-- imply
  ∏ i : N, ∑' k, p i k =
  ∑' f : (i : N) → S i, ∏ i : N, p i (f i) := by
-- proof
  apply prod_tsum_eq_tsum_prod_finset'_discrete p hp

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma prod_finset_tsum_eq_tsum_prod_eq
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [DiscreteTopology K]
  [DecidableEq I]
  {S : I → Type*}
  (s : Finset I)
  (p : (i : I) → S i → K⟦X⟧)
  (hp : ∀ i ∈ s, Summable (p i)) :
-- imply
  ∏ i ∈ s, ∑' k : S i, p i k = ∑' f : (i : s) → S i, ∏ i : s, p i (f i) := by
-- proof
  apply prod_finset_tsum_eq_tsum_prod s p hp

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma tprod_tsum_eq_tsum_prod_essentially_finite_eq
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [DiscreteTopology K]
  {S : I → Type*} [∀ i, Zero (S i)] [∀ i, DecidableEq (S i)]
  (p : (i : I) → S i → K⟦X⟧)
  (hp_zero : ∀ i, p i 0 = 1)
  (hp_summable : Summable fun ik : (Σ i, Subtype (fun k : S i => k ≠ 0)) => p ik.1 ik.2.1) :
-- imply
  (tprod fun i : I => ∑' k : S i, p i k) =
  ∑' f : (Subtype fun f : (i : I) → S i => ∀ᶠ i in Filter.cofinite, f i = 0),
    (tprod fun i : I => p i (f.val i)) := by
-- proof
  apply tprod_tsum_eq_tsum_prod_essentiallyFinite p hp_zero hp_summable

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma tprod_tsum_eq_tsum_prod_essentially_finite_nat_eq
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [DiscreteTopology K]
  {S : PNat → Type*} [∀ i, Zero (S i)] [∀ i, DecidableEq (S i)]
  (p : (i : PNat) → S i → K⟦X⟧)
  (hp_zero : ∀ i, p i 0 = 1)
  (hp_summable : Summable fun ik : SBar S => p ik.1 ik.2.1) :
-- imply
  (tprod fun i : PNat => ∑' k : S i, p i k) =
  ∑' f : (Subtype fun f : (i : PNat) → S i => ∀ᶠ i in Filter.cofinite, f i = 0),
    (tprod fun i : PNat => p i (f.val i)) := by
-- proof
  apply tprod_tsum_eq_tsum_prod_essentiallyFinite_nat p hp_zero hp_summable

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma coeff_mul_tprod_one_add_eq_coeff_le
  [CommRing K]
  [TopologicalSpace K]
  [T2Space K]
  (a : K⟦X⟧)
  (f : J → K⟦X⟧)
  (hf_summable : Summable f)
  (n : ℕ)
  (hf_order : ∀ i : J, ∀ m ≤ n, (PowerSeries.coeff m) (f i) = 0) :
-- imply
  ∀ m ≤ n, (PowerSeries.coeff m) (a * (tprod fun i => (1 + f i))) =
  (PowerSeries.coeff m) a := by
-- proof
  apply coeff_mul_tprod_one_add_eq_coeff a f hf_summable n hf_order

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma euler_odd_parts_identity_eq
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [NoZeroDivisors K] :
-- imply
  (tprod fun i : PNat =>
    Ring.inverse (1 - (PowerSeries.X : K⟦X⟧) ^ (2 * (i : ℕ) - 1))) =
  (tprod fun k : PNat => (1 + (PowerSeries.X : K⟦X⟧) ^ (k : ℕ))) := by
-- proof
  apply euler_odd_parts_identity

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma euler_odd_parts_identity'_eq
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [NoZeroDivisors K] :
-- imply
  (tprod fun i : (Subtype fun n : PNat => Odd (n : ℕ)) =>
    Ring.inverse (1 - (PowerSeries.X : K⟦X⟧) ^ (i : ℕ))) =
  (tprod fun k : PNat => (1 + (PowerSeries.X : K⟦X⟧) ^ (k : ℕ))) := by
-- proof
  apply euler_odd_parts_identity'

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma euler_distinct_odd_partitions_eq
  (n : ℕ) :
-- imply
  numDistinctPartitions n = numOddPartitions n := by
-- proof
  apply euler_distinct_odd_partitions n

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma continuous_rescale_eq
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  (a : K) :
-- imply
  Continuous (PowerSeries.rescale a : K⟦X⟧ → K⟦X⟧) := by
-- proof
  apply continuous_rescale a

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma tprod_rescale_substitution_eq
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  (f : I → K⟦X⟧)
  (a : K)
  (hf : Multipliable f) :
-- imply
  PowerSeries.rescale a (tprod fun i => f i) =
  (tprod fun i => PowerSeries.rescale a (f i)) := by
-- proof
  apply tprod_rescale_substitution f a hf

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma binary_product_rule_eq
  [CommRing K]
  [TopologicalSpace K]
  [DiscreteTopology K]
  (a : ℕ → K⟦X⟧)
  (ha : Summable a) :
-- imply
  (tprod fun i : ℕ => (1 + a i)) =
  ∑' s : Finset ℕ, ∏ i ∈ s, a i := by
-- proof
  apply binary_product_rule a ha

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma binary_product_rule'_eq
  [CommRing K]
  [TopologicalSpace K]
  [DiscreteTopology K]
  (a : ℕ → K⟦X⟧)
  (ha : Summable a) :
-- imply
  (tprod fun i : ℕ => (1 + a i)) =
  ∑' J : (Subtype fun J : Set ℕ => J.Finite),
    (finprod fun i => (finprod fun (_ : i ∈ J.val) => a i)) := by
-- proof
  apply binary_product_rule' a ha

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma x_coeff_finProd_eq_zero_of_factor_high_order
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  {n : ℕ}
  {S : Fin n → Type*}
-- given
  (p : (i : Fin n) → S i → K⟦X⟧)
  (f : (i : Fin n) → S i)
  (i : Fin n)
  (d : ℕ)
  (h : ∀ m ≤ d, PowerSeries.coeff m (p i (f i)) = 0) :
-- imply
  PowerSeries.coeff d (∏ j : Fin n, p j (f j)) = 0 := by
-- proof
  apply _root_.coeff_finProd_eq_zero_of_factor_high_order p f i d h

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma x_summable_prod_of_summable_discrete
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [DiscreteTopology K]
-- given
  (f : α → K⟦X⟧)
  (g : β → K⟦X⟧)
  (hf : Summable f)
  (hg : Summable g) :
-- imply
  Summable (fun p : α × β => f p.1 * g p.2) := by
-- proof
  apply _root_.summable_prod_of_summable_discrete f g hf hg

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma x_multipliable_of_essentiallyFinite
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  {S : I → Type*} [∀ i, Zero (S i)] [∀ i, DecidableEq (S i)]
-- given
  (p : (i : I) → S i → K⟦X⟧)
  (hp_zero : ∀ i, p i 0 = 1)
  (f : Subtype (fun f : (i : I) → S i => ∀ᶠ i in Filter.cofinite, f i = 0)) :
-- imply
  Multipliable fun i => p i (f.val i) := by
-- proof
  apply _root_.multipliable_of_essentiallyFinite p hp_zero f

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma x_summable_comp_injective_of_discrete
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [DiscreteTopology K]
  {f : α → K}
  {g : β → α}
-- given
  (hf : Summable f)
  (hg : Function.Injective g) :
-- imply
  Summable (f ∘ g) := by
-- proof
  apply _root_.summable_comp_injective_of_discrete hf hg

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma x_T'n_finite_of_discrete
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [DiscreteTopology K]
  {S : I → Type*} [∀ i, Zero (S i)] [∀ i, DecidableEq (S i)]
-- given
  (p : (i : I) → S i → K⟦X⟧)
  (hp_summable : Summable fun ik : Σ i, Subtype (fun k : S i => k ≠ 0) => p ik.1 ik.2.1)
  (n : ℕ) :
-- imply
  { ik : Σ i, Subtype (fun k : S i => k ≠ 0) | ∃ m ≤ n, PowerSeries.coeff m (p ik.1 ik.2.val) ≠ 0 }.Finite := by
-- proof
  apply _root_.T'n_finite_of_discrete p hp_summable n

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma x_coeff_prod_eq_zero_of_factor_coeff_zero
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [DecidableEq I]
-- given
  (s : Finset I)
  (f : I → K⟦X⟧)
  (j : I)
  (n : ℕ)
  (hj : j ∈ s)
  (hf : ∀ m ≤ n, PowerSeries.coeff m (f j) = 0) :
-- imply
  ∀ m ≤ n, PowerSeries.coeff m (∏ i ∈ s, f i) = 0 := by
-- proof
  apply _root_.coeff_prod_eq_zero_of_factor_coeff_zero s f j hj n hf

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma x_finite_funcs_with_graph_in_finite_set
  {S : I → Type*} [∀ i, Zero (S i)] [∀ i, DecidableEq (S i)]
-- given
  (T : Set (Σ i, Subtype (fun k : S i => k ≠ 0)))
  (hT : T.Finite) :
-- imply
  { f : Subtype (fun f : (i : I) → S i => ∀ᶠ i in Filter.cofinite, f i = 0) | ∀ i, (hi : f.val i ≠ 0) → ⟨i, ⟨f.val i, hi⟩⟩ ∈ T }.Finite := by
-- proof
  apply _root_.finite_funcs_with_graph_in_finite_set T hT

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma x_summable_tsum_nonzero_fiber_discrete
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [DiscreteTopology K]
  {S : I → Type*} [∀ i, Zero (S i)] [∀ i, DecidableEq (S i)]
-- given
  (p : (i : I) → S i → K⟦X⟧)
  (hp_summable : Summable fun ik : Σ i, Subtype (fun k : S i => k ≠ 0) => p ik.1 ik.2.1) :
-- imply
  Summable fun i => ∑' k : Subtype (fun k : S i => k ≠ 0), p i k.1 := by
-- proof
  apply _root_.summable_tsum_nonzero_fiber_discrete p hp_summable

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma x_multipliable_tsum_fiber_discrete
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [DiscreteTopology K]
  {S : I → Type*} [∀ i, Zero (S i)] [∀ i, DecidableEq (S i)]
-- given
  (p : (i : I) → S i → K⟦X⟧)
  (hp_zero : ∀ i, p i 0 = 1)
  (hp_summable : Summable fun ik : Σ i, Subtype (fun k : S i => k ≠ 0) => p ik.1 ik.2.1) :
-- imply
  Multipliable fun i => ∑' k : S i, p i k := by
-- proof
  apply _root_.multipliable_tsum_fiber_discrete p hp_zero hp_summable

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma x_summable_prod_essentiallyFinite_discrete
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [DiscreteTopology K]
  {S : I → Type*} [∀ i, Zero (S i)] [∀ i, DecidableEq (S i)]
-- given
  (p : (i : I) → S i → K⟦X⟧)
  (hp_zero : ∀ i, p i 0 = 1)
  (hp_summable : Summable fun ik : Σ i, Subtype (fun k : S i => k ≠ 0) => p ik.1 ik.2.1) :
-- imply
  Summable fun f : Subtype (fun f : (i : I) → S i => ∀ᶠ i in Filter.cofinite, f i = 0) => tprod (fun i : I => p i (f.val i)) := by
-- proof
  apply _root_.summable_prod_essentiallyFinite_discrete p hp_zero hp_summable

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma x_summable_prod_essentiallyFinite
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [DiscreteTopology K]
  {S : I → Type*} [∀ i, Zero (S i)] [∀ i, DecidableEq (S i)]
-- given
  (p : (i : I) → S i → K⟦X⟧)
  (hp_zero : ∀ i, p i 0 = 1)
  (hp_summable : Summable fun ik : Σ i, Subtype (fun k : S i => k ≠ 0) => p ik.1 ik.2.1) :
-- imply
  Summable fun f : Subtype (fun f : (i : I) → S i => ∀ᶠ i in Filter.cofinite, f i = 0) => tprod (fun i : I => p i (f.val i)) := by
-- proof
  apply _root_.summable_prod_essentiallyFinite p hp_zero hp_summable

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma x_coeff_prod_eq_of_extra_high_order'
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [DecidableEq I]
-- given
  (g : I → K⟦X⟧)
  (s t : Finset I)
  (n : ℕ)
  (hst : s ⊆ t)
  (h_high_order : ∀ i ∈ t \ s, ∀ m ≤ n, PowerSeries.coeff m (g i) = 0) :
-- imply
  PowerSeries.coeff n (∏ i ∈ t, (1 + g i)) = PowerSeries.coeff n (∏ i ∈ s, (1 + g i)) := by
-- proof
  apply _root_.coeff_prod_eq_of_extra_high_order' g s t hst n h_high_order

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma x_coeff_tprod_one_add_eq_coeff_prod_of_high_order'
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [DiscreteTopology K]
-- given
  (g : I → K⟦X⟧)
  (I_n : Set I)
  (n : ℕ)
  (hI_n : I_n.Finite)
  (hmult : Multipliable (1 + g ·))
  (h_high_order : ∀ i ∉ I_n, ∀ m ≤ n, PowerSeries.coeff m (g i) = 0) :
-- imply
  PowerSeries.coeff n (tprod (fun i => (1 + g i))) = PowerSeries.coeff n (∏ i ∈ hI_n.toFinset, (1 + g i)) := by
-- proof
  apply _root_.coeff_tprod_one_add_eq_coeff_prod_of_high_order' g I_n hI_n hmult n h_high_order

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma x_extendToI_essentiallyFinite
  {S : I → Type*} [∀ i, Zero (S i)]
  {I_n : Set I}
-- given
  (hI_n_finite : I_n.Finite)
  (f : (i : hI_n_finite.toFinset) → S i) :
-- imply
  ∀ᶠ i in Filter.cofinite, extendToI hI_n_finite f i = 0 := by
-- proof
  apply _root_.extendToI_essentiallyFinite hI_n_finite f

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma x_restrictToI_n_extendToI_subtype
  {S : I → Type*} [∀ i, Zero (S i)]
  {I_n : Set I}
-- given
  (hI_n_finite : I_n.Finite)
  (f : (i : hI_n_finite.toFinset) → S i) :
-- imply
  restrictToI_n hI_n_finite (extendToI_subtype hI_n_finite f) = f := by
-- proof
  apply _root_.restrictToI_n_extendToI_subtype hI_n_finite f

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma x_extendToI_subtype_restrictToI_n
  {S : I → Type*} [∀ i, Zero (S i)]
  {I_n : Set I}
-- given
  (f : Subtype (fun f : (i : I) → S i => ∀ᶠ i in Filter.cofinite, f i = 0))
  (hI_n_finite : I_n.Finite)
  (hf_supp : ∀ i, f.val i ≠ 0 → i ∈ I_n) :
-- imply
  extendToI_subtype hI_n_finite (restrictToI_n hI_n_finite f) = f := by
-- proof
  apply _root_.extendToI_subtype_restrictToI_n hI_n_finite f hf_supp

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma x_prod_eq_tprod_extendToI
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  {S : I → Type*} [∀ i, Zero (S i)]
  {I_n : Set I}
-- given
  (p : (i : I) → S i → K⟦X⟧)
  (hI_n_finite : I_n.Finite)
  (hp_zero : ∀ i, p i 0 = 1)
  (f : (i : hI_n_finite.toFinset) → S i) :
-- imply
  ∏ i : hI_n_finite.toFinset, p i (f i) = tprod (fun i : I => p i (extendToI hI_n_finite f i)) := by
-- proof
  apply _root_.prod_eq_tprod_extendToI hI_n_finite p hp_zero f

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma x_oddPNatEquivPNat_symm_coe
-- given
  (i : PNat) :
-- imply
  (oddPNatEquivPNat.symm i : ℕ) = 2 * i - 1 := by
-- proof
  apply _root_.oddPNatEquivPNat_symm_coe i

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma x_summable_fiber_discrete
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [DiscreteTopology K]
  {S : I → Type*} [∀ i, Zero (S i)] [∀ i, DecidableEq (S i)]
-- given
  (p : (i : I) → S i → K⟦X⟧)
  (hp_summable : Summable fun ik : Σ i, Subtype (fun k : S i => k ≠ 0) => p ik.1 ik.2.1)
  (i : I) :
-- imply
  Summable (p i) := by
-- proof
  apply _root_.summable_fiber_discrete p hp_summable i

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma x_summable_fiber
  [CommRing K]
  [UniformSpace K]
  [IsUniformAddGroup K]
  [IsTopologicalRing K]
  [CompleteSpace K]
  {S : I → Type*} [∀ i, Zero (S i)] [∀ i, DecidableEq (S i)]
-- given
  (p : (i : I) → S i → K⟦X⟧)
  (hp_summable : Summable fun ik : Σ i, Subtype (fun k : S i => k ≠ 0) => p ik.1 ik.2.1)
  (i : I) :
-- imply
  Summable (p i) := by
-- proof
  apply _root_.summable_fiber p hp_summable i

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma pv_tsum_mul_tsum_eq_tsum_prod_swap
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
-- given
  (f : α → K⟦X⟧)
  (g : β → K⟦X⟧)
  (hf : Summable f)
  (hg : Summable g)
  (hfg : Summable (fun p : α × β => f p.1 * g p.2)) :
-- imply
  (∑' a, f a) * (∑' b, g b) = ∑' p : β × α, f p.2 * g p.1 := by
-- proof
  apply _root_.tsum_mul_tsum_eq_tsum_prod_swap f g hf hg hfg

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma pv_coeff_prod_eq_zero_of_factor_coeff_zero_aux
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [DecidableEq I]
-- given
  (s : Finset I)
  (f : I → K⟦X⟧)
  (j : I)
  (n : ℕ)
  (hj : j ∈ s)
  (hf : ∀ m ≤ n, coeff m (f j) = 0) :
-- imply
  ∀ m ≤ n, coeff m (∏ i ∈ s, f i) = 0 := by
-- proof
  apply _root_.coeff_prod_eq_zero_of_factor_coeff_zero_aux s f j hj n hf

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma pv_summable_ps_finite_support_coeff
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [DiscreteTopology K]
-- given
  (f : α → K⟦X⟧)
  (hf : Summable f)
  (d : ℕ) :
-- imply
  (Function.support (fun a => coeff d (f a))).Finite := by
-- proof
  apply _root_.summable_ps_finite_support_coeff f hf d

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma pv_summable_prod_of_summable
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [DiscreteTopology K]
-- given
  (f : α → K⟦X⟧)
  (g : β → K⟦X⟧)
  (hf : Summable f)
  (hg : Summable g) :
-- imply
  Summable (fun p : α × β => f p.1 * g p.2) := by
-- proof
  apply _root_.summable_prod_of_summable f g hf hg

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma pv_summable_prod_fin
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [DiscreteTopology K]
  {n : ℕ}
  {S : Fin n → Type*}
-- given
  (p : (i : Fin n) → S i → K⟦X⟧)
  (hp : ∀ i, Summable (p i)) :
-- imply
  Summable (fun f : (i : Fin n) → S i => ∏ i : Fin n, p i (f i)) := by
-- proof
  apply _root_.summable_prod_fin p hp

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma pv_indicator_complete
  [AddCommGroup R]
  [UniformSpace R]
  [IsUniformAddGroup R]
  [CompleteSpace R]
  {f : α → R}
-- given
  (hf : Summable f)
  (s : Set α) :
-- imply
  Summable (s.indicator f) := by
-- proof
  apply _root_.Summable.indicator_complete hf s

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma pv_coeff_prod_one_add_eq_coeff_one_of_high_order
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [DecidableEq J]
-- given
  (s : Finset J)
  (f : J → K⟦X⟧)
  (n : ℕ)
  (hf_order : ∀ i ∈ s, (n : ENat) < order (f i)) :
-- imply
  ∀ m ≤ n, coeff m (∏ i ∈ s, (1 + f i)) = coeff m (1 : K⟦X⟧) := by
-- proof
  apply _root_.coeff_prod_one_add_eq_coeff_one_of_high_order s f n hf_order

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma pv_coeff_tprod_one_add_eq_coeff_one
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
-- given
  (f : J → K⟦X⟧)
  (n : ℕ)
  (hmult : Multipliable (1 + f ·))
  (hf_order : ∀ i : J, (n : ENat) < order (f i)) :
-- imply
  ∀ m ≤ n, PowerSeries.coeff m (tprod (fun i => (1 + f i))) = PowerSeries.coeff m (1 : K⟦X⟧) := by
-- proof
  apply _root_.coeff_tprod_one_add_eq_coeff_one f hmult n hf_order

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma pv_Ring_inverse_one_sub_X_pow
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [NoZeroDivisors K]
-- given
  (k : ℕ)
  (hk : k ≠ 0) :
-- imply
  Ring.inverse (1 - (X : K⟦X⟧)^k) = ∑' j : ℕ, (X : K⟦X⟧) ^ (k * j) := by
-- proof
  apply _root_.Ring_inverse_one_sub_X_pow k hk

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma pv_rhs_eq_genFun
  [CommRing K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [T2Space K]
  [NoZeroDivisors K] :
-- imply
  tprod (fun k : PNat => (1 + (X : K⟦X⟧) ^ (k : ℕ))) = PowerSeries.mk fun n => ((Nat.Partition.countRestricted n 2).card : K) := by
-- proof
  apply _root_.rhs_eq_genFun

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma pv_restricted_Odd_eq
-- given
  (n : ℕ) :
-- imply
  Nat.Partition.restricted n Odd = Nat.Partition.restricted n (¬ 2 ∣ ·) := by
-- proof
  apply _root_.restricted_Odd_eq n

/--
[InfiniteProducts2](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/InfiniteProducts2.lean)
-/
@[path]
private lemma pv_pnatEquivEvenNat_value
-- given
  (j : PNat) :
-- imply
  2 * (j : ℕ) - 1 = (pnatEquivEvenNat j).val + 1 := by
-- proof
  apply _root_.pnatEquivEvenNat_value j


-- created on 2026-10-11
-- updated on 2026-10-23
