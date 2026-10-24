import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.Valuation.DiscreteValuationBook
open Polynomial


namespace Definitions
end Definitions
/--
[TopologicalGroupProp.of_isTopologicalGroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/DiscreteValuationBook.lean)
-/
@[path]
private lemma TopologicalGroupProp.of_isTopologicalGroup
  {G : Type*}
  [TopologicalSpace G]
  [Group G]
  [IsTopologicalGroup G] :
-- imply
  TopologicalGroupProp G :=
-- proof
  ⟨continuous_mul, continuous_inv⟩

/--
[TopologicalGroupProp.toIsTopologicalGroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/DiscreteValuationBook.lean)
-/
@[path]
private lemma TopologicalGroupProp.toIsTopologicalGroup
  [TopologicalSpace G]
  [Group G]
-- given
  (h : TopologicalGroupProp G) :
-- imply
  IsTopologicalGroup G :=
-- proof
  { continuous_mul := h.mul_continuous
    continuous_inv := h.inv_continuous }
section ClopenSubsets
universe u v
variable (K : Type u) [Field K] {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]
  [hv : Valued K Γ₀]

/--
[valuationRing_isOpen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/DiscreteValuationBook.lean)
-/
@[path]
private lemma valuationRing_isOpen
  {K : Type u}
  [Field K]
  {Γ₀ : Type v}
  [LinearOrderedCommGroupWithZero Γ₀] :
-- imply
  IsOpen (hv.v.valuationSubring : Set K) :=
-- proof
  Valued.isOpen_valuationSubring K

/--
[valuationRing_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/DiscreteValuationBook.lean)
-/
@[path]
private lemma valuationRing_isClosed
  {K : Type u}
  [Field K]
  {Γ₀ : Type v}
  [LinearOrderedCommGroupWithZero Γ₀] :
-- imply
  IsClosed (hv.v.valuationSubring : Set K) :=
-- proof
  Valued.isClosed_valuationSubring K

/--
[valuationRing_isClopen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/DiscreteValuationBook.lean)
-/
@[path]
private lemma valuationRing_isClopen
  {K : Type u}
  [Field K]
  {Γ₀ : Type v}
  [LinearOrderedCommGroupWithZero Γ₀] :
-- imply
  IsClopen (hv.v.valuationSubring : Set K) :=
-- proof
  ⟨valuationRing_isClosed K, valuationRing_isOpen K⟩

/--
[maximalIdeal_isOpen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/DiscreteValuationBook.lean)
-/
@[path]
private lemma maximalIdeal_isOpen
  {K : Type u}
  [Field K]
  {Γ₀ : Type v}
  [LinearOrderedCommGroupWithZero Γ₀] :
-- imply
  IsOpen (X := K) {x | Valued.v.restrict x < (1 : MonoidWithZeroHom.ValueGroup₀ hv.v)} :=
-- proof
  Valued.isOpen_ball K 1

/--
[maximalIdeal_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/DiscreteValuationBook.lean)
-/
@[path]
private lemma maximalIdeal_isClosed
  {K : Type u}
  [Field K]
  {Γ₀ : Type v}
  [LinearOrderedCommGroupWithZero Γ₀] :
-- imply
  IsClosed (X := K) {x | Valued.v.restrict x < (1 : MonoidWithZeroHom.ValueGroup₀ hv.v)} :=
-- proof
  Valued.isClosed_ball K 1

/--
[maximalIdeal_isClopen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/DiscreteValuationBook.lean)
-/
@[path]
private lemma maximalIdeal_isClopen
  {K : Type u}
  [Field K]
  {Γ₀ : Type v}
  [LinearOrderedCommGroupWithZero Γ₀] :
-- imply
  IsClopen (X := K) {x | Valued.v.restrict x < (1 : MonoidWithZeroHom.ValueGroup₀ hv.v)} :=
-- proof
  ⟨maximalIdeal_isClosed K, maximalIdeal_isOpen K⟩

/--
[valuationUnits_isOpen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/DiscreteValuationBook.lean)
-/
@[path]
private lemma valuationUnits_isOpen
  {K : Type u}
  [Field K]
  {Γ₀ : Type v}
  [LinearOrderedCommGroupWithZero Γ₀] :
-- imply
  IsOpen (X := K) {x | Valued.v.restrict x = (1 : MonoidWithZeroHom.ValueGroup₀ hv.v)} :=
-- proof
  Valued.isOpen_sphere K one_ne_zero

/--
[valuationUnits_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/DiscreteValuationBook.lean)
-/
@[path]
private lemma valuationUnits_isClosed
  {K : Type u}
  [Field K]
  {Γ₀ : Type v}
  [LinearOrderedCommGroupWithZero Γ₀] :
-- imply
  IsClosed (X := K) {x | Valued.v.restrict x = (1 : MonoidWithZeroHom.ValueGroup₀ hv.v)} :=
-- proof
  Valued.isClosed_sphere K 1

/--
[valuationUnits_isClopen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/DiscreteValuationBook.lean)
-/
@[path]
private lemma valuationUnits_isClopen
  {K : Type u}
  [Field K]
  {Γ₀ : Type v}
  [LinearOrderedCommGroupWithZero Γ₀] :
-- imply
  IsClopen (X := K) {x | Valued.v.restrict x = (1 : MonoidWithZeroHom.ValueGroup₀ hv.v)} :=
-- proof
  ⟨valuationUnits_isClosed K, valuationUnits_isOpen K⟩
end ClopenSubsets
section HenselsLemma

/--
[hensel_nonmonic_adic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/DiscreteValuationBook.lean)
-/
@[path]
private lemma hensel_nonmonic_adic
  {R : Type*}
  [CommRing R]
  {I : Ideal R}
  [IsAdicComplete I R]
  {f : R[X]}
  {a₀ : R}
-- given
  (h₁ : f.eval a₀ ∈ I)
  (h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
-- imply
  ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ I := by
-- proof
  classical
  let f' := derivative f
  let c : ℕ → R := fun n =>
    Nat.recOn n a₀ fun _ b => b - f.eval b * Ring.inverse (f'.eval b)
  have hc : ∀ n, c (n + 1) = c n - f.eval (c n) * Ring.inverse (f'.eval (c n)) := by
    intro n; simp only [c]
  have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [hc, sub_eq_add_neg, ← add_zero a₀]
      refine ih.add ?_
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine I.mul_mem_right _ ?_
      rw [← SModEq.zero] at h₁ ⊢
      exact (ih.eval f).trans h₁
  have hf'c : ∀ n, IsUnit (f'.eval (c n)) := by
    intro n
    haveI := isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    convert h₂ using 1
    exact SModEq.def.mp ((hc_mod n).eval _)
  have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa [Nat.rec_zero, zero_add, pow_one] using h₁
    | succ n ih =>
      rw [← taylor_eval_sub (c n), hc, sub_eq_add_neg, sub_eq_add_neg,
        add_neg_cancel_comm]
      rw [eval_eq_sum, sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two), ←
        Finset.sum_range_add_sum_Ico _ (Nat.le_add_left _ _)]
      swap
      · intro i; rw [zero_mul]
      refine Ideal.add_mem _ ?_ ?_
      · rw [← one_add_one_eq_two, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
        taylor_coeff_zero, taylor_coeff_one, pow_zero, pow_one, mul_one, mul_neg,
        mul_left_comm, Ring.mul_inverse_cancel _ (hf'c n), mul_one, add_neg_cancel]
        exact Ideal.zero_mem _
      · refine Submodule.sum_mem _ ?_
        simp only [Finset.mem_Ico]
        rintro i ⟨h2i, _⟩
        have aux : n + 2 ≤ i * (n + 1) := by trans 2 * (n + 1) <;> nlinarith [h2i]
        refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right aux ?_)
        rw [pow_mul']
        exact Ideal.pow_mem_pow ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ ih) _
  have cauchy : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := by
    intro m n hmn
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    clear hmn
    induction k with
    | zero => simp [SModEq.refl]
    | succ k ih =>
      rw [← Nat.add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
      refine ih.add ?_
      symm
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right ?_ (hfcI _))
      rwa [Nat.add_assoc]
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (cauchy _ _)
  refine ⟨a, ?_, ?_⟩
  · show f.IsRoot a
    suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal R)] by exact IsHausdorff.haus' _ this
    intro n
    specialize ha n
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
    refine (ha.symm.eval f).trans ?_
    rw [SModEq.zero]
    exact Ideal.pow_le_pow_right le_self_add (hfcI _)
  · show a - a₀ ∈ I
    specialize ha (0 + 1)
    rw [hc, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, sub_eq_add_neg] at ha
    rw [← SModEq.sub_mem, ← add_zero a₀]
    refine ha.symm.trans (SModEq.rfl.add ?_)
    rw [SModEq.zero, Ideal.neg_mem_iff]
    exact Ideal.mul_mem_right _ _ h₁

/--
[hensel_nonmonic_adic_newton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/DiscreteValuationBook.lean)
-/
@[path]
private lemma hensel_nonmonic_adic_newton
  {R : Type*}
  [CommRing R]
  {I : Ideal R}
  [IsAdicComplete I R]
  {f : R[X]}
  {a₀ : R}
-- given
  (h₁ : f.eval a₀ ∈ I)
  (h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
-- imply
  ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ I ∧ (∀ n, newtonSeq f a₀ n ≡ a [SMOD (I ^ n • ⊤ : Ideal R)]) ∧ (∀ n, f.eval (newtonSeq f a₀ n) ∈ I ^ (n + 1)) ∧ (∀ n, IsUnit ((Polynomial.derivative f).eval (newtonSeq f a₀ n))) := by
-- proof
  classical
  set c := newtonSeq f a₀ with hc_def
  have hc : ∀ n, c (n + 1) = c n - f.eval (c n) * Ring.inverse ((derivative f).eval (c n)) := by
    intro n; simp only [c, newtonSeq]
  have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [hc, sub_eq_add_neg, ← add_zero a₀]
      refine ih.add ?_
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine I.mul_mem_right _ ?_
      rw [← SModEq.zero] at h₁ ⊢
      exact (ih.eval f).trans h₁
  have hf'c : ∀ n, IsUnit ((derivative f).eval (c n)) := by
    intro n
    haveI := isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    convert h₂ using 1
    exact SModEq.def.mp ((hc_mod n).eval _)
  have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa [Nat.rec_zero, zero_add, pow_one] using h₁
    | succ n ih =>
      rw [← taylor_eval_sub (c n), hc, sub_eq_add_neg, sub_eq_add_neg,
        add_neg_cancel_comm]
      rw [eval_eq_sum, sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two), ←
        Finset.sum_range_add_sum_Ico _ (Nat.le_add_left _ _)]
      swap
      · intro i; rw [zero_mul]
      refine Ideal.add_mem _ ?_ ?_
      · rw [← one_add_one_eq_two, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
        taylor_coeff_zero, taylor_coeff_one, pow_zero, pow_one, mul_one, mul_neg,
        mul_left_comm, Ring.mul_inverse_cancel _ (hf'c n), mul_one, add_neg_cancel]
        exact Ideal.zero_mem _
      · refine Submodule.sum_mem _ ?_
        simp only [Finset.mem_Ico]
        rintro i ⟨h2i, _⟩
        have aux : n + 2 ≤ i * (n + 1) := by trans 2 * (n + 1) <;> nlinarith [h2i]
        refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right aux ?_)
        rw [pow_mul']
        exact Ideal.pow_mem_pow ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ ih) _
  have cauchy : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := by
    intro m n hmn
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    clear hmn
    induction k with
    | zero => simp [SModEq.refl]
    | succ k ih =>
      rw [← Nat.add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
      refine ih.add ?_
      symm
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right ?_ (hfcI _))
      rwa [Nat.add_assoc]
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (cauchy _ _)
  refine ⟨a, ?_, ?_, ha, hfcI, hf'c⟩
  · show f.IsRoot a
    suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal R)] by exact IsHausdorff.haus' _ this
    intro n
    specialize ha n
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
    refine (ha.symm.eval f).trans ?_
    rw [SModEq.zero]
    exact Ideal.pow_le_pow_right le_self_add (hfcI _)
  · show a - a₀ ∈ I
    specialize ha (0 + 1)
    rw [hc, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, sub_eq_add_neg] at ha
    rw [← SModEq.sub_mem, ← add_zero a₀]
    refine ha.symm.trans (SModEq.rfl.add ?_)
    rw [SModEq.zero, Ideal.neg_mem_iff]
    exact Ideal.mul_mem_right _ _ h₁
end HenselsLemma


-- created on 2026-10-24
