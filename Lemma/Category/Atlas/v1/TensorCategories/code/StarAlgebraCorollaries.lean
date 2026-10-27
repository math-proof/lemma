import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TensorCategories.code.StarAlgebraCorollaries.Part3
open Finset Complex FusionRing FusionRing.GrRingOfC


namespace FusionRing

/--
[grStarC_basisVecC](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma grStarC_basisVecC
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {i : ι} :
-- imply
  R.grStarC (basisVecC i) = basisVecC (R.star i) := by
-- proof
  funext j
  unfold grStarC basisVecC
  simp only [apply_ite (starRingEnd ℂ), map_one, map_zero]
  congr 1
  exact propext ⟨fun h => by rw [← h, R.star_star], fun h => by rw [h, R.star_star]⟩

end FusionRing

namespace FusionRing

/--
[basisVecC_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma basisVecC_ne_zero
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {i : ι} :
-- imply
  basisVecC i ≠ (0 : ι → ℂ) := by
-- proof
  intro h
  have : (basisVecC i : ι → ℂ) i = (0 : ι → ℂ) i := congrFun h i
  unfold basisVecC at this
  simp at this

end FusionRing

namespace FusionRing

/--
[grMulC_basisVecC_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma grMulC_basisVecC_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {i j k : ι} :
-- imply
  R.grMulC (basisVecC i) (basisVecC j) k = (R.N i j k : ℂ) := by
-- proof
  unfold grMulC basisVecC
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    sum_ite_eq', mem_univ, if_true]

end FusionRing

namespace FusionRing

/--
[grTraceC_basisVecC_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma grTraceC_basisVecC_mul
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {i j : ι} :
-- imply
  R.grTraceC (R.grMulC (basisVecC i) (basisVecC j)) = (R.N i j R.unit : ℂ) := by
-- proof
  unfold grTraceC
  exact R.grMulC_basisVecC_eq i j R.unit

end FusionRing

namespace FusionRing

/--
[N_self_star_unit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma N_self_star_unit
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {i : ι} :
-- imply
  R.N i (R.star i) R.unit = 1 := by
-- proof
  rw [R.duality]; simp

end FusionRing

namespace FusionRing

/--
[grMulC_basisVecC_dual_trace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma grMulC_basisVecC_dual_trace
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {i : ι} :
-- imply
  R.grTraceC (R.grMulC (basisVecC i) (basisVecC (R.star i))) = 1 := by
-- proof
  rw [R.grTraceC_basisVecC_mul, R.N_self_star_unit]; simp

end FusionRing

namespace FusionRing

/--
[grTraceC_basisVecC_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma grTraceC_basisVecC_val
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {i : ι} :
-- imply
  R.grTraceC (basisVecC i) = if i = R.unit then 1 else 0 := by
-- proof
  unfold grTraceC basisVecC
  by_cases h : R.unit = i
  · simp [h]
  · simp [h, Ne.symm h]

end FusionRing

namespace FusionRing

/--
[grTraceC_basisVecC_unit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma grTraceC_basisVecC_unit
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι} :
-- imply
  R.grTraceC (basisVecC R.unit) = 1 := by
-- proof
  rw [grTraceC_basisVecC_val]; simp

end FusionRing

namespace FusionRing

/--
[grPowC_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma grPowC_zero
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {f : ι → ℂ}
  {k : ι} :
-- imply
  grPowC R f 0 k = if k = R.unit then 1 else 0 :=
-- proof
  rfl

end FusionRing

namespace FusionRing

/--
[grPowC_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma grPowC_succ
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {f : ι → ℂ}
  {n : ℕ} :
-- imply
  grPowC R f (n + 1) = R.grMulC (grPowC R f n) f :=
-- proof
  rfl

end FusionRing

namespace FusionRing

/--
[grMulC_one_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma grMulC_one_left
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {f : ι → ℂ} :
-- imply
  R.grMulC (fun k => if k = R.unit then 1 else 0) f = f := by
-- proof
  funext k; unfold grMulC
  simp_rw [ite_mul, one_mul, zero_mul]
  conv_lhs => arg 2; ext i; rw [show (∑ j, (if i = R.unit then f j * (R.N i j k : ℂ)
    else 0)) = if i = R.unit then ∑ j, f j * (R.N i j k : ℂ) else 0
    from by split <;> simp_all]
  simp_rw [sum_ite_eq', mem_univ, if_true]
  simp_rw [R.unit_mul, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true]

end FusionRing

namespace FusionRing

/--
[grPowC_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma grPowC_one
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {f : ι → ℂ} :
-- imply
  grPowC R f 1 = f := by
-- proof
  show R.grMulC (fun k => if k = R.unit then 1 else 0) f = f
  exact R.grMulC_one_left f

end FusionRing

namespace FusionRing

/--
[exists_pos_trace_power_unit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma exists_pos_trace_power_unit
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι} :
-- imply
  ∃ n : ℕ, 0 < n ∧ 0 < (R.grTraceC (grPowC R (basisVecC R.unit) n)).re := by
-- proof
  refine ⟨1, Nat.one_pos, ?_⟩
  rw [grPowC_one]
  rw [R.grTraceC_basisVecC_unit]
  norm_num

end FusionRing

namespace FusionRing

/--
[exists_pos_trace_power_selfdual](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma exists_pos_trace_power_selfdual
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {i : ι}
-- given
  (hsd : R.star i = i) :
-- imply
  ∃ n : ℕ, 0 < n ∧ 0 < (R.grTraceC (grPowC R (basisVecC i) n)).re := by
-- proof
  refine ⟨2, by omega, ?_⟩
  show 0 < (R.grTraceC (R.grMulC (R.grMulC (fun k => if k = R.unit then 1 else 0)
    (basisVecC i)) (basisVecC i))).re
  rw [R.grMulC_one_left]
  rw [R.grTraceC_basisVecC_mul, R.duality, hsd, if_pos rfl]
  norm_num

end FusionRing

namespace FusionRing

/--
[trace_basis_product_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma trace_basis_product_pos
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {i : ι} :
-- imply
  0 < (R.grTraceC (R.grMulC (basisVecC i) (basisVecC (R.star i)))).re := by
-- proof
  rw [R.grTraceC_basisVecC_mul, R.N_self_star_unit]
  norm_num

end FusionRing

namespace FusionRing

/--
[exists_pos_trace_power](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma exists_pos_trace_power
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {i : ι}
-- given
  (hi : i = R.unit ∨ R.star i = i) :
-- imply
  ∃ n : ℕ, 0 < n ∧ 0 < (R.grTraceC (grPowC R (basisVecC i) n)).re := by
-- proof
  obtain rfl | hsd := hi
  · exact R.exists_pos_trace_power_unit
  · exact R.exists_pos_trace_power_selfdual i hsd

end FusionRing

namespace FusionRing

/--
[grTraceC_grPowC_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma grTraceC_grPowC_succ
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {i : ι}
  {n : ℕ} :
-- imply
  R.grTraceC (grPowC R (basisVecC i) (n + 1)) = grPowC R (basisVecC i) n (R.star i) := by
-- proof
  unfold grTraceC
  show (R.grMulC (grPowC R (basisVecC i) n) (basisVecC i)) R.unit = _
  unfold grMulC basisVecC
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [R.duality]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_ite, mul_one, mul_zero]
  conv_lhs =>
    arg 2; ext j
    rw [show (if i = R.star j then grPowC R (fun k => if k = i then 1 else 0) n j
      else 0) =
      (if j = R.star i then grPowC R (fun k => if k = i then 1 else 0) n j
        else 0)
      from by
        congr 1
        exact propext ⟨fun h => by rw [← R.star_star j, h],
          fun h => by rw [h, R.star_star]⟩]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

end FusionRing

namespace FusionRing

/--
[grPowC_basisVecC_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma grPowC_basisVecC_nonneg
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {i : ι}
  {n : ℕ}
  {k : ι} :
-- imply
  ∃ m : ℕ, grPowC R (basisVecC i) n k = (m : ℂ) := by
-- proof
  induction n generalizing k with
  | zero =>
    use if k = R.unit then 1 else 0
    simp only [grPowC]
    split <;> simp
  | succ n ih =>
    show ∃ m : ℕ, (R.grMulC (grPowC R (basisVecC i) n) (basisVecC i)) k = ↑m
    unfold grMulC basisVecC
    simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    suffices ∃ m : ℕ, ∑ j : ι, grPowC R (fun l => if l = i then 1 else 0) n j *
      (R.N j i k : ℂ) = (m : ℂ) by exact this
    have : ∀ j, ∃ mj : ℕ, grPowC R (fun l => if l = i then 1 else 0) n j *
      (R.N j i k : ℂ) = (mj : ℂ) := by
      intro j
      obtain ⟨c, hc⟩ := ih j
      exact ⟨c * R.N j i k, by push_cast; unfold basisVecC at hc; rw [hc]⟩
    choose mj hmj using this
    exact ⟨∑ j : ι, mj j, by push_cast; exact Finset.sum_congr rfl (fun j _ => hmj j)⟩

end FusionRing

namespace FusionRing

/--
[grPowC_basisVecC_succ_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma grPowC_basisVecC_succ_ne_zero
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {i : ι}
  {n : ℕ}
-- given
  (hn : ∃ k : ι, 0 < (grPowC R (basisVecC i) n k).re) :
-- imply
  ∃ k : ι, 0 < (grPowC R (basisVecC i) (n + 1) k).re := by
-- proof
  obtain ⟨j, hj⟩ := hn
  obtain ⟨m, _, hm⟩ := Finset.exists_lt_of_sum_lt
    (show ∑ _k : ι, (0 : ℕ) < ∑ k : ι, R.N j i k by
      simp only [Finset.sum_const_zero]; exact R.sum_N_pos j i)
  use m
  show 0 < ((R.grMulC (grPowC R (basisVecC i) n) (basisVecC i)) m).re
  unfold grMulC basisVecC
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Complex.re_sum, Complex.mul_re, Complex.natCast_im, mul_zero, sub_zero,
    Complex.natCast_re, Complex.re_ofNat]
  apply lt_of_lt_of_le _ (Finset.sum_le_sum (fun l _ => le_refl _))
  apply lt_of_lt_of_le _ (Finset.single_le_sum (f := fun l => (grPowC R (fun k => if k = i then (1 : ℂ) else 0) n l).re * (R.N l i m : ℝ)) (fun l _ => ?_) (Finset.mem_univ j))
  · apply mul_pos hj
    exact Nat.cast_pos.mpr (by omega)
  ·
    apply mul_nonneg
    · obtain ⟨c, hc⟩ := R.grPowC_basisVecC_nonneg i n l
      unfold basisVecC at hc
      rw [hc]; simp [Nat.cast_nonneg]
    · exact Nat.cast_nonneg _

end FusionRing

namespace FusionRing

/--
[grPowC_basisVecC_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma grPowC_basisVecC_ne_zero
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {i : ι}
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  ∃ k : ι, 0 < (grPowC R (basisVecC i) n k).re := by
-- proof
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      use i
      rw [R.grPowC_one]
      unfold basisVecC
      simp
    | succ m =>
      exact R.grPowC_basisVecC_succ_ne_zero i (m + 1) (ih (by omega))

end FusionRing

namespace FusionRing

/--
[sum_ite_const_zeroC](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma sum_ite_const_zeroC
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  [AddCommMonoid α]
  {p : Prop}
  [Decidable p]
  {s : Finset ι'}
  {f : ι' → α} :
-- imply
  (∑ x ∈ s, if p then f x else 0) = if p then ∑ x ∈ s, f x else 0 := by
-- proof
  split <;> simp_all

end FusionRing

namespace FusionRing

/--
[assoc_complex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma assoc_complex
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {i j k l : ι} :
-- imply
  (univ.sum fun m => (R.N i j m : ℂ) * (R.N m k l : ℂ)) = (univ.sum fun m => (R.N j k m : ℂ) * (R.N i m l : ℂ)) := by
-- proof
  exact_mod_cast R.assoc i j k l

end FusionRing

namespace FusionRing

/--
[unit_mul_complex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma unit_mul_complex
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {j k : ι} :
-- imply
  (R.N R.unit j k : ℂ) = if j = k then 1 else 0 := by
-- proof
  rw [R.unit_mul]; split <;> simp

end FusionRing

namespace FusionRing

/--
[mul_unit_complex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma mul_unit_complex
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {i k : ι} :
-- imply
  (R.N i R.unit k : ℂ) = if i = k then 1 else 0 := by
-- proof
  rw [R.mul_unit]; split <;> simp

end FusionRing

namespace FusionRing

/--
[grMulC_one_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma grMulC_one_right
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {f : ι → ℂ} :
-- imply
  R.grMulC f (fun k => if k = R.unit then 1 else 0) = f := by
-- proof
  funext k; unfold grMulC
  simp_rw [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    sum_ite_eq', mem_univ, if_true, R.mul_unit_complex,
    mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true]

end FusionRing

namespace FusionRing

/--
[inner_sum_eqC](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma inner_sum_eqC
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {a b c : ι → ℂ}
  {l i j k : ι} :
-- imply
  (∑ m : ι, a i * (b j * (c k * ((R.N i j m : ℂ) * (R.N m k l : ℂ))))) = (∑ q : ι, a i * (b j * (c k * ((R.N j k q : ℂ) * (R.N i q l : ℂ))))) := by
-- proof
  simp_rw [← Finset.mul_sum]
  congr 3
  exact R.assoc_complex i j k l

end FusionRing

namespace FusionRing

/--
[grMulC_assoc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma grMulC_assoc
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {a b c : ι → ℂ} :
-- imply
  R.grMulC (R.grMulC a b) c = R.grMulC a (R.grMulC b c) := by
-- proof
  funext l; simp only [grMulC]
  simp_rw [mul_assoc, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  trans (∑ i : ι, ∑ j, ∑ k, ∑ m,
    a i * (b j * (c k * ((R.N i j m : ℂ) * (R.N m k l : ℂ)))))
  · rw [Finset.sum_comm]
    conv_lhs => arg 2; ext _; rw [Finset.sum_comm]
    conv_lhs => arg 2; ext _; arg 2; ext _; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext _; rw [Finset.sum_comm]
    congr 1; ext i; congr 1; ext j; congr 1; ext k; congr 1; ext m; ring
  · conv_rhs => arg 2; ext _; rw [Finset.sum_comm]
    conv_rhs => arg 2; ext _; arg 2; ext _; rw [Finset.sum_comm]
    congr 1; ext i; congr 1; ext j; congr 1; ext k
    exact R.inner_sum_eqC a b c l i j k

end FusionRing

namespace FusionRing

/--
[grMulC_left_distrib](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma grMulC_left_distrib
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {a b c : ι → ℂ} :
-- imply
  R.grMulC a (fun k => b k + c k) = fun k => R.grMulC a b k + R.grMulC a c k := by
-- proof
  funext l; simp only [grMulC]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]

end FusionRing

namespace FusionRing

/--
[grMulC_right_distrib](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma grMulC_right_distrib
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {a b c : ι → ℂ} :
-- imply
  R.grMulC (fun k => a k + b k) c = fun k => R.grMulC a c k + R.grMulC b c k := by
-- proof
  funext l; simp only [grMulC]
  simp_rw [add_mul, Finset.sum_add_distrib]

end FusionRing

namespace FusionRing

/--
[grMulC_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma grMulC_zero
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {a : ι → ℂ} :
-- imply
  R.grMulC a (fun _ => 0) = fun _ => 0 := by
-- proof
  funext l; simp only [grMulC]; simp

end FusionRing

namespace FusionRing

/--
[grZeroC_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma grZeroC_mul
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {a : ι → ℂ} :
-- imply
  R.grMulC (fun _ => 0) a = fun _ => 0 := by
-- proof
  funext l; simp only [grMulC]; simp

end FusionRing

namespace FusionRing

/--
[grMulC_smul_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma grMulC_smul_left
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {c : ℂ}
  {a b : ι → ℂ} :
-- imply
  R.grMulC (fun k => c * a k) b = fun k => c * R.grMulC a b k := by
-- proof
  funext l; simp only [grMulC]
  simp_rw [mul_assoc, Finset.mul_sum]

end FusionRing

namespace FusionRing

/--
[N_cyclic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma N_cyclic
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {i j k : ι} :
-- imply
  R.N i j (R.star k) = R.N j k (R.star i) := by
-- proof
  have h := R.assoc i j k R.unit
  simp only [R.duality] at h
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  have : ∀ x : ι, (k = R.star x) = (x = R.star k) :=
    fun x => propext ⟨fun h => by rw [← R.star_star x, h], fun h => by rw [h, R.star_star]⟩
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  exact h

end FusionRing

namespace FusionRing

/--
[N_star_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma N_star_reverse
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {i j k : ι} :
-- imply
  R.N (R.star j) (R.star i) k = R.N i j (R.star k) := by
-- proof
  rw [R.N_star_transpose (R.star j) (R.star i) k, R.star_star]
  rw [R.N_cyclic i j k]

end FusionRing

namespace FusionRing

/--
[grMulC_scalar_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma grMulC_scalar_left
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {c : ℂ}
  {f : ι → ℂ} :
-- imply
  R.grMulC (fun k => if k = R.unit then c else 0) f = fun k => c * R.grMulC (fun k => if k = R.unit then 1 else 0) f k := by
-- proof
  funext l; unfold grMulC
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.mul_sum]
  congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j
  split <;> ring

end FusionRing

namespace FusionRing

/--
[grMulC_scalar_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma grMulC_scalar_right
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {c : ℂ}
  {f : ι → ℂ} :
-- imply
  R.grMulC f (fun k => if k = R.unit then c else 0) = fun k => c * R.grMulC f (fun k => if k = R.unit then 1 else 0) k := by
-- proof
  funext l; unfold grMulC
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.mul_sum]
  congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j
  split <;> ring

end FusionRing

namespace FusionRing

/--
[complexified_grothendieck_ring_semisimple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma complexified_grothendieck_ring_semisimple
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι} :
-- imply
  IsSemisimpleRing (GrRingOfC R) :=
-- proof
  @StarAlgWithTrace.starAlgWithTrace_isSemisimple R.grStarAlgWithTrace
    GrRingOfC.instFiniteDimensional

end FusionRing

namespace FusionRing

/--
[GrRingOfC_pow_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma GrRingOfC_pow_coeff
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {i : ι}
  {n : ℕ} :
-- imply
  ((⟨basisVecC i⟩ : GrRingOfC R) ^ n).coeff = grPowC R (basisVecC i) n := by
-- proof
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ]
    show (R.grMulC ((⟨basisVecC i⟩ : GrRingOfC R) ^ n).coeff (basisVecC i)) =
      R.grMulC (grPowC R (basisVecC i) n) (basisVecC i)
    rw [ih]

end FusionRing

namespace FusionRing

/--
[GrRingOfC_traceLinMap_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma GrRingOfC_traceLinMap_pow
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {i : ι}
  {n : ℕ} :
-- imply
  GrRingOfC.traceLinMap (R := R) ((⟨basisVecC i⟩ : GrRingOfC R) ^ n) = R.grTraceC (grPowC R (basisVecC i) n) := by
-- proof
  show R.grTraceC ((⟨basisVecC i⟩ : GrRingOfC R) ^ n).coeff =
    R.grTraceC (grPowC R (basisVecC i) n)
  rw [GrRingOfC_pow_coeff]

end FusionRing

namespace FusionRing

/--
[trace_aeval_eq_sum_GrRingOfC](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma trace_aeval_eq_sum_GrRingOfC
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {p : Polynomial ℂ}
  {x : GrRingOfC R} :
-- imply
  GrRingOfC.traceLinMap (R := R) (Polynomial.aeval x p) = p.sum (fun n (a : ℂ) => a * GrRingOfC.traceLinMap (R := R) (x ^ n)) := by
-- proof
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum, Polynomial.sum]
  rw [map_sum]
  congr 1
  ext n
  show GrRingOfC.traceLinMap (R := R) ((algebraMap ℂ (GrRingOfC R)) (p.coeff n) * x ^ n) =
    p.coeff n * GrRingOfC.traceLinMap (R := R) (x ^ n)
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]

end FusionRing

namespace FusionRing

/--
[trace_aeval_zero_of_zero_const](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma trace_aeval_zero_of_zero_const
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {p : Polynomial ℂ}
  {x : GrRingOfC R}
-- given
  (hp0 : p.coeff 0 = 0)
  (hτ : ∀ n : ℕ, 0 < n → GrRingOfC.traceLinMap (R := R) (x ^ n) = 0) :
-- imply
  GrRingOfC.traceLinMap (R := R) (Polynomial.aeval x p) = 0 := by
-- proof
  rw [trace_aeval_eq_sum_GrRingOfC]
  apply Finset.sum_eq_zero
  intro n hn
  show p.coeff n * GrRingOfC.traceLinMap (R := R) (x ^ n) = 0
  by_cases h0 : n = 0
  · subst h0; simp [hp0]
  · rw [hτ n (Nat.pos_of_ne_zero h0), mul_zero]

end FusionRing

namespace FusionRing

/--
[exists_nonzero_idempotent_poly_of_not_nilpotent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma exists_nonzero_idempotent_poly_of_not_nilpotent
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  [Ring A]
  [Algebra ℂ A]
  [FiniteDimensional ℂ A]
  {x : A}
-- given
  (hx : ¬IsNilpotent x) :
-- imply
  ∃ (p : Polynomial ℂ), p.coeff 0 = 0 ∧ IsIdempotentElem (Polynomial.aeval x p) ∧ Polynomial.aeval x p ≠ 0 := by
-- proof
  by_cases h0 : (minpoly ℂ x).eval 0 = 0
  ·
    set mp := minpoly ℂ x with hmp_def
    have hmp_ne : mp ≠ 0 := minpoly.ne_zero (IsIntegral.of_finite ℂ x)
    set k := mp.rootMultiplicity 0 with hk_def
    have hk_pos : 0 < k := by
      rw [hk_def, Polynomial.rootMultiplicity_pos hmp_ne]; exact h0
    obtain ⟨q, hfact, hq_ndvd⟩ := mp.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hmp_ne (0 : ℂ)
    simp only [map_zero, sub_zero] at hfact hq_ndvd
    have hq_ne : q ≠ 0 := by intro hq0; rw [hq0, mul_zero] at hfact; exact hmp_ne hfact
    have hcop : IsCoprime (Polynomial.X ^ k : Polynomial ℂ) q := by
      rw [isCoprime_comm]
      exact (Polynomial.irreducible_X (R := ℂ)).coprime_pow_of_not_dvd k hq_ndvd
    obtain ⟨u, v, huv⟩ := hcop
    have hef_sum : Polynomial.aeval x (u * Polynomial.X ^ k) +
      Polynomial.aeval x (v * q) = 1 := by
      rw [← map_add, huv]; simp
    have hef_prod : Polynomial.aeval x (u * Polynomial.X ^ k) *
      Polynomial.aeval x (v * q) = 0 := by
      rw [← map_mul]
      have : u * Polynomial.X ^ k * (v * q) = u * v * (Polynomial.X ^ k * q) := by ring
      rw [this, ← hfact, hmp_def, map_mul, minpoly.aeval, mul_zero]
    refine ⟨u * Polynomial.X ^ k, ?_, ?_, ?_⟩
    ·
      rw [Polynomial.coeff_mul]
      apply Finset.sum_eq_zero
      intro ⟨i, j⟩ hij
      simp only [Finset.mem_antidiagonal] at hij
      have hi : i = 0 := (Nat.eq_zero_of_add_eq_zero hij).1
      have hj : j = 0 := (Nat.eq_zero_of_add_eq_zero hij).2
      subst hi; subst hj
      have : (Polynomial.X ^ k : Polynomial ℂ).coeff 0 = 0 := by
        rw [Polynomial.coeff_X_pow, if_neg]; omega
      simp [this]
    ·
      rw [IsIdempotentElem]
      have : Polynomial.aeval x (u * Polynomial.X ^ k) *
        (Polynomial.aeval x (u * Polynomial.X ^ k) +
          Polynomial.aeval x (v * q)) =
        Polynomial.aeval x (u * Polynomial.X ^ k) * 1 := by rw [hef_sum]
      rwa [mul_add, hef_prod, add_zero, mul_one] at this
    ·
      intro he0
      apply hx
      have hf1 : Polynomial.aeval x (v * q) = 1 := by
        have := hef_sum; rw [he0, zero_add] at this; exact this
      rw [map_mul] at hf1
      have hq_unit : IsUnit (Polynomial.aeval x q) := by
        have hcomm : Polynomial.aeval x q * Polynomial.aeval x v = 1 := by
          have heq : Polynomial.aeval x v * Polynomial.aeval x q =
            Polynomial.aeval x q * Polynomial.aeval x v := by
            simp [← map_mul, mul_comm]
          rw [← heq]; exact hf1
        exact ⟨⟨Polynomial.aeval x q, Polynomial.aeval x v, hcomm, hf1⟩, rfl⟩
      have hmpx : Polynomial.aeval x (Polynomial.X ^ k * q) = 0 := by
        rw [← hfact, hmp_def]; exact minpoly.aeval ℂ x
      simp only [map_mul, map_pow, Polynomial.aeval_X] at hmpx
      exact ⟨k, (hq_unit.mul_left_eq_zero).mp hmpx⟩
  ·
    have hXndvd : ¬(Polynomial.X : Polynomial ℂ) ∣ minpoly ℂ x := by
      intro ⟨q, hq⟩; exact h0 (by simp [hq])
    have hcop : IsCoprime (Polynomial.X : Polynomial ℂ) (minpoly ℂ x) :=
      (Polynomial.irreducible_X).coprime_iff_not_dvd.mpr hXndvd
    obtain ⟨u, v, huv⟩ := hcop
    have haeval : Polynomial.aeval x (u * Polynomial.X) = 1 := by
      have h1 : Polynomial.aeval x (u * Polynomial.X + v * minpoly ℂ x) =
        Polynomial.aeval x (1 : Polynomial ℂ) := by rw [huv]
      simp [map_add, map_mul, minpoly.aeval] at h1
      simp [map_mul, Polynomial.aeval_X]; exact h1
    refine ⟨u * Polynomial.X, ?_, ?_, ?_⟩
    · simp [Polynomial.coeff_mul, Polynomial.coeff_X]
    · rw [IsIdempotentElem, haeval, mul_one]
    · rw [haeval]
      intro h1eq0
      apply hx
      have : Subsingleton A := subsingleton_of_zero_eq_one (h1eq0.symm)
      exact ⟨1, Subsingleton.elim _ _⟩
/-- Corollary 1.43.6: for any basis element `i` of a fusion ring, some positive power has
positive real trace. Combine the idempotent-polynomial construction with positive definiteness
of the trace on `GrRingOfC R`. -/
end


/--
[corollary_1_43_5_fusion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
lemma corollary_1_43_5_fusion
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι} :
-- imply
  IsSemisimpleRing (FusionRing.GrRingOfC R) :=
-- proof
  R.complexified_grothendieck_ring_semisimple

/--
[coeff_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
private lemma coeff_zero_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {R : FusionRing ι}
  {k : ι} :
-- imply
  (0 : GrRingOfC R).coeff k = 0 := by
-- proof
  apply FusionRing.GrRingOfC.coeff_zero R k

/--
[coeff_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
private lemma coeff_one_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {R : FusionRing ι}
  {k : ι} :
-- imply
  (1 : GrRingOfC R).coeff k = if k = R.unit then 1 else 0 := by
-- proof
  apply FusionRing.GrRingOfC.coeff_one R k

/--
[coeff_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
private lemma coeff_add_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {R : FusionRing ι}
  {a b : GrRingOfC R}
  {k : ι} :
-- imply
  (a + b).coeff k = a.coeff k + b.coeff k := by
-- proof
  apply FusionRing.GrRingOfC.coeff_add R a b k

/--
[coeff_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
private lemma coeff_neg_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {R : FusionRing ι}
  {a : GrRingOfC R}
  {k : ι} :
-- imply
  (-a).coeff k = -a.coeff k := by
-- proof
  apply FusionRing.GrRingOfC.coeff_neg R a k

/--
[coeff_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean)
-/
@[path]
private lemma coeff_sub_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {R : FusionRing ι}
  {a b : GrRingOfC R}
  {k : ι} :
-- imply
  (a - b).coeff k = a.coeff k - b.coeff k := by
-- proof
  apply FusionRing.GrRingOfC.coeff_sub R a b k


-- created on 2026-10-23
