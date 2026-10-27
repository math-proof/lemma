import Mathlib
import Initialize.Tactic.Attr.Basic
import Class.v1.Atlas.Buildings.code.Valuation.LatticesValuations
open Polynomial Matrix DVRContext Metric Set


namespace Definitions
end Definitions
namespace DVRContext

/--
[isUnitInO_isInO](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/LatticesValuations.lean)
-/
@[path]
private lemma isUnitInO_isInO
  {C : DVRContext}
  {x : C.k}
-- given
  (h : C.isUnitInO x) :
-- imply
  C.isInO x := by
-- proof
  obtain ⟨r, _, hr⟩ := h
  exact ⟨r, hr⟩

end DVRContext

namespace DVRContext

/--
[isInMaxIdeal_isInO](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/LatticesValuations.lean)
-/
@[path]
private lemma isInMaxIdeal_isInO
  {C : DVRContext}
  {x : C.k}
-- given
  (h : C.isInMaxIdeal x) :
-- imply
  C.isInO x := by
-- proof
  obtain ⟨r, _, hr⟩ := h
  exact ⟨r, hr⟩

end DVRContext

namespace DVRContext

/--
[HenselsLemma](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/LatticesValuations.lean)
-/
@[path]
private lemma HenselsLemma
  {C : DVRContext}
  [IsLocalRing C.𝔬]
  [IsAdicComplete (IsLocalRing.maximalIdeal C.𝔬) C.𝔬] :
-- imply
  ∀ (f : C.𝔬[X]) (a₀ : C.𝔬), f.eval a₀ ∈ IsLocalRing.maximalIdeal C.𝔬 → (Polynomial.derivative f).eval a₀ ∉ IsLocalRing.maximalIdeal C.𝔬 → ∃ a : C.𝔬, f.eval a = 0 ∧ a - a₀ ∈ IsLocalRing.maximalIdeal C.𝔬 ∧ (∀ n, f.eval (C.newtonSeq f a₀ n) ∈ (IsLocalRing.maximalIdeal C.𝔬) ^ (n + 1)) ∧ (∀ n, IsUnit ((Polynomial.derivative f).eval (C.newtonSeq f a₀ n))) := by
-- proof
  intro f a₀ h1 h2
  have h_unit_R : IsUnit ((Polynomial.derivative f).eval a₀) := by
    rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at h2
  have h_unit : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal C.𝔬)
    ((Polynomial.derivative f).eval a₀)) := h_unit_R.map _
  classical
  set I := IsLocalRing.maximalIdeal C.𝔬
  set c := C.newtonSeq f a₀
  have hc : ∀ n, c (n + 1) = c n - f.eval (c n) *
    Ring.inverse ((Polynomial.derivative f).eval (c n)) := by
    intro n
    simp only [c, newtonSeq]
  have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [hc, sub_eq_add_neg, ← add_zero a₀]
      refine ih.add ?_
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine I.mul_mem_right _ ?_
      rw [← SModEq.zero] at h1 ⊢
      exact (ih.eval f).trans h1
  have hf'c : ∀ n, IsUnit ((derivative f).eval (c n)) := by
    intro n
    have := isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    convert h_unit using 1
    exact (SModEq.def).mp ((hc_mod n).eval _)
  have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      simpa [c, newtonSeq, Nat.rec_zero, zero_add, pow_one] using h1
    | succ n ih =>
      rw [← taylor_eval_sub (c n), hc, sub_eq_add_neg, sub_eq_add_neg, add_neg_cancel_comm]
      rw [eval_eq_sum, sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two),
        ← Finset.sum_range_add_sum_Ico _ (Nat.le_add_left _ _)]
      swap; · intro i; rw [zero_mul]
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
  have cauchy : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal C.𝔬)] := by
    intro m n hmn
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    clear hmn; induction k with
    | zero => simp [SModEq.refl]
    | succ k ih =>
      rw [← Nat.add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
      refine ih.add ?_
      symm; rw [SModEq.zero, Ideal.neg_mem_iff]
      refine Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right ?_ (hfcI _))
      rw [Nat.add_assoc]; exact le_self_add
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (cauchy _ _)
  refine ⟨a, ?_, ?_, hfcI, hf'c⟩
  · show f.IsRoot a
    suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal C.𝔬)] by
      exact IsHausdorff.haus' _ this
    intro n; specialize ha n
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
    exact Ideal.mul_mem_right _ _ h1

end DVRContext

namespace DVRContext

/--
[isInO_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/LatticesValuations.lean)
-/
@[path]
private lemma isInO_sum
  {C : DVRContext}
  [DVRClosure C]
  {s : Finset ι}
  {f : ι → C.k}
-- given
  (hf : ∀ i ∈ s, C.isInO (f i)) :
-- imply
  C.isInO (∑ i ∈ s, f i) := by
-- proof
  induction s using Finset.cons_induction with
  | empty =>
    simp
    exact DVRClosure.isInO_zero
  | cons a s has ih =>
    rw [Finset.sum_cons]
    exact DVRClosure.isInO_add (hf a (Finset.mem_cons_self a s))
      (ih (fun i hi => hf i (Finset.mem_cons_of_mem hi)))

end DVRContext

namespace DVRContext

/--
[isInO_prod](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/LatticesValuations.lean)
-/
@[path]
private lemma isInO_prod
  {C : DVRContext}
  [DVRClosure C]
  {s : Finset ι}
  {f : ι → C.k}
-- given
  (hf : ∀ i ∈ s, C.isInO (f i)) :
-- imply
  C.isInO (∏ i ∈ s, f i) := by
-- proof
  induction s using Finset.cons_induction with
  | empty =>
    simp
    exact DVRClosure.isInO_one
  | cons a s has ih =>
    rw [Finset.prod_cons]
    exact DVRClosure.isInO_mul (hf a (Finset.mem_cons_self a s))
      (ih (fun i hi => hf i (Finset.mem_cons_of_mem hi)))

end DVRContext

namespace DVRContext

/--
[det_isInO](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/LatticesValuations.lean)
-/
@[path]
private lemma det_isInO
  {C : DVRContext}
  [DVRClosure C]
  {m : ℕ}
  {A : Matrix (Fin m) (Fin m) C.k}
-- given
  (hA : ∀ i j, C.isInO (A i j)) :
-- imply
  C.isInO A.det := by
-- proof
  rw [Matrix.det_apply]
  apply isInO_sum; intro σ _
  simp only [Units.smul_def, zsmul_eq_mul]
  exact DVRClosure.isInO_mul (DVRClosure.isInO_intCast _)
    (isInO_prod (fun i _ => hA (σ i) i))

end DVRContext

namespace DVRContext

/--
[adjugate_isInO](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/LatticesValuations.lean)
-/
@[path]
private lemma adjugate_isInO
  {C : DVRContext}
  [DVRClosure C]
  {m : ℕ}
  {A : Matrix (Fin m) (Fin m) C.k}
-- given
  (hA : ∀ i j, C.isInO (A i j)) :
-- imply
  ∀ i j, C.isInO (A.adjugate i j) := by
-- proof
  intro i j
  rw [Matrix.adjugate_apply]
  apply det_isInO; intro a b
  simp only [Matrix.updateRow_apply]
  split
  · simp only [Pi.single_apply]; split
    · exact DVRClosure.isInO_one
    · exact DVRClosure.isInO_zero
  · exact hA a b

end DVRContext

namespace DVRContext

/--
[nonsing_inv_isInO](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/LatticesValuations.lean)
-/
@[path]
private lemma nonsing_inv_isInO
  {C : DVRContext}
  [DVRClosure C]
  {m : ℕ}
  {A : Matrix (Fin m) (Fin m) C.k}
-- given
  (hA : ∀ i j, C.isInO (A i j))
  (hdet : C.isUnitInO A.det) :
-- imply
  ∀ i j, C.isInO (A⁻¹ i j) := by
-- proof
  intro i j
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  exact DVRClosure.isInO_mul (DVRClosure.isUnitInO_inv hdet) (adjugate_isInO (A := A) hA i j)

end DVRContext

namespace DVRContext

/--
[isClopen_valuationRing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/LatticesValuations.lean)
-/
@[path]
private lemma isClopen_valuationRing
  {C : DVRContext}
  [DVRClosure C]
  [ht : DVRTopology C] :
-- imply
  @IsClopen C.k ht.instNormedField.toUniformSpace.toTopologicalSpace {x : C.k | C.isInO x} := by
-- proof
  let : NormedField C.k := ht.instNormedField
  let : Field C.k := NormedField.toField (α := C.k)
  let : IsUltrametricDist C.k := ht.instUltrametric
  have heq : {x : C.k | C.isInO x} = closedBall (0 : C.k) 1 := by
    ext x
    simp [ht.isInO_iff_norm_le_one, Metric.mem_closedBall, dist_eq_norm, sub_zero]
  rw [heq]
  exact IsUltrametricDist.isClopen_closedBall 0 one_ne_zero

end DVRContext

namespace DVRContext

/--
[isClopen_maximalIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/LatticesValuations.lean)
-/
@[path]
private lemma isClopen_maximalIdeal
  {C : DVRContext}
  [DVRClosure C]
  [ht : DVRTopology C] :
-- imply
  @IsClopen C.k ht.instNormedField.toUniformSpace.toTopologicalSpace {x : C.k | C.isInMaxIdeal x} := by
-- proof
  let : NormedField C.k := ht.instNormedField
  let : Field C.k := NormedField.toField (α := C.k)
  let : IsUltrametricDist C.k := ht.instUltrametric
  have heq : {x : C.k | C.isInMaxIdeal x} = ball (0 : C.k) 1 := by
    ext x
    simp [ht.isInMaxIdeal_iff_norm_lt_one, Metric.mem_ball, dist_eq_norm, sub_zero]
  rw [heq]
  exact IsUltrametricDist.isClopen_ball 0 1

end DVRContext

namespace DVRContext

/--
[isClopen_units](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/LatticesValuations.lean)
-/
@[path]
private lemma isClopen_units
  {C : DVRContext}
  [DVRClosure C]
  [ht : DVRTopology C] :
-- imply
  @IsClopen C.k ht.instNormedField.toUniformSpace.toTopologicalSpace {x : C.k | C.isUnitInO x} := by
-- proof
  let : NormedField C.k := ht.instNormedField
  let : Field C.k := NormedField.toField (α := C.k)
  let : IsUltrametricDist C.k := ht.instUltrametric
  have heq : {x : C.k | C.isUnitInO x} =
      closedBall (0 : C.k) 1 \ ball (0 : C.k) 1 := by
    ext x
    simp only [Set.mem_ofPred, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
      ht.isUnitInO_iff_norm_eq_one, dist_eq_norm, sub_zero]
    constructor
    · intro h
      exact ⟨le_of_eq h, not_lt.mpr (ge_of_eq h)⟩
    · intro ⟨h1, h2⟩
      exact le_antisymm h1 (not_lt.mp h2)
  rw [heq]
  exact (IsUltrametricDist.isClopen_closedBall (0 : C.k) one_ne_zero).diff
    (IsUltrametricDist.isClopen_ball (0 : C.k) 1)

end DVRContext

namespace DVRContext

/--
[isClopen_valuationRing_units_maxIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/LatticesValuations.lean)
-/
@[path]
private lemma isClopen_valuationRing_units_maxIdeal
  {C : DVRContext}
  [DVRClosure C]
  [ht : DVRTopology C] :
-- imply
  @IsClopen C.k ht.instNormedField.toUniformSpace.toTopologicalSpace {x : C.k | C.isInO x} ∧ @IsClopen C.k ht.instNormedField.toUniformSpace.toTopologicalSpace {x : C.k | C.isUnitInO x} ∧ @IsClopen C.k ht.instNormedField.toUniformSpace.toTopologicalSpace {x : C.k | C.isInMaxIdeal x} := by
-- proof
  exact ⟨isClopen_valuationRing, isClopen_units, isClopen_maximalIdeal⟩

end DVRContext


-- created on 2026-10-24
