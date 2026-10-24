import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ProjectionTheory.code.SelbergExpansion
open Matrix Finset BigOperators SelbergExpansion


namespace SelbergExpansion

/--
[groupConv_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SelbergExpansion.lean)
-/
@[path]
lemma groupConv_reflect
  [Fintype G]
  [DecidableEq G]
  [Group G]
  {f₁ f₂ : G → ℂ}
  {x : G} :
-- imply
  groupConv f₁ f₂ x⁻¹ = groupConv (fun g => f₂ g⁻¹) (fun g => f₁ g⁻¹) x := by
-- proof
  simp only [groupConv]
  refine (Fintype.sum_equiv (Equiv.mulLeft x⁻¹) _ _ (fun h => ?_)).symm
  simp only [Equiv.coe_mulLeft]
  have h1 : (h⁻¹ * x)⁻¹ = x⁻¹ * h := by group
  have h2 : (x⁻¹ * h)⁻¹ * x⁻¹ = h⁻¹ := by group
  rw [h1, h2, mul_comm]

end SelbergExpansion

namespace SelbergExpansion

/--
[groupConv_assoc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SelbergExpansion.lean)
-/
@[path]
lemma groupConv_assoc
  [Fintype G]
  [DecidableEq G]
  [Group G]
  {f₁ f₂ f₃ : G → ℂ} :
-- imply
  groupConv (groupConv f₁ f₂) f₃ = groupConv f₁ (groupConv f₂ f₃) := by
-- proof
  ext g
  simp only [groupConv, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  congr 1; ext g₁
  rw [show (∑ x : G, f₁ g₁ * (f₂ x * f₃ (x⁻¹ * (g₁⁻¹ * g)))) =
    ∑ x : G, f₁ g₁ * (f₂ (g₁⁻¹ * x) * f₃ (x⁻¹ * g)) from by
    rw [← Equiv.sum_comp (Equiv.mulLeft g₁⁻¹)]
    congr 1; ext x; simp only [Equiv.coe_mulLeft]; congr 2; group]

end SelbergExpansion

namespace SelbergExpansion

/--
[groupConv_delta_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SelbergExpansion.lean)
-/
@[path]
lemma groupConv_delta_right
  [Fintype G]
  [DecidableEq G]
  [Group G]
  {f : G → ℂ} :
-- imply
  groupConv f (fun g => if g = 1 then 1 else 0) = f := by
-- proof
  ext g; simp only [groupConv]
  rw [Fintype.sum_eq_single g (fun b hb => by
    have : b⁻¹ * g ≠ 1 := by intro h; apply hb; rwa [inv_mul_eq_one] at h
    simp [this])]
  simp [inv_mul_cancel]

end SelbergExpansion

namespace SelbergExpansion

/--
[groupConv_delta_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SelbergExpansion.lean)
-/
@[path]
lemma groupConv_delta_left
  [Fintype G]
  [DecidableEq G]
  [Group G]
  {f : G → ℂ} :
-- imply
  groupConv (fun g => if g = 1 then 1 else 0) f = f := by
-- proof
  ext g; simp only [groupConv]
  rw [Fintype.sum_eq_single 1 (fun b hb => by simp [hb])]; simp

end SelbergExpansion

namespace SelbergExpansion

/--
[groupConv_comm_convPow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SelbergExpansion.lean)
-/
@[path]
lemma groupConv_comm_convPow
  [Fintype G]
  [DecidableEq G]
  [Group G]
  {μ : G → ℂ}
  {n : ℕ} :
-- imply
  groupConv μ (convPow μ n) = groupConv (convPow μ n) μ := by
-- proof
  induction n with
  | zero =>
    simp only [convPow]
    rw [groupConv_delta_left, groupConv_delta_right]
  | succ n ih =>
    show groupConv μ (groupConv (convPow μ n) μ) = groupConv (groupConv (convPow μ n) μ) μ
    rw [← groupConv_assoc, ih]

end SelbergExpansion

namespace SelbergExpansion

/--
[convPow_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SelbergExpansion.lean)
-/
@[path]
lemma convPow_symmetric
  [Fintype G]
  [DecidableEq G]
  [Group G]
  {μ : G → ℂ}
  {K : ℕ}
-- given
  (hμ : IsSymmetricMeasure μ) :
-- imply
  ∀ g : G, convPow μ K g = convPow μ K g⁻¹ := by
-- proof
  induction K with
  | zero => intro g; simp [convPow, inv_eq_one]
  | succ n ih =>
    intro g
    show groupConv (convPow μ n) μ g = groupConv (convPow μ n) μ g⁻¹
    rw [groupConv_reflect]
    have hμ_eq : (fun g => μ g⁻¹) = μ := by ext h; exact (hμ h).symm
    have hf_eq : (fun g => convPow μ n g⁻¹) = convPow μ n := by ext h; exact (ih h).symm
    rw [hμ_eq, hf_eq, groupConv_comm_convPow]

end SelbergExpansion

namespace SelbergExpansion

/--
[convPow_conj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SelbergExpansion.lean)
-/
@[path]
lemma convPow_conj
  [Fintype G]
  [DecidableEq G]
  [Group G]
  {μ : G → ℂ}
  {K : ℕ}
-- given
  (hreal : ∀ g, starRingEnd ℂ (μ g) = μ g) :
-- imply
  ∀ g, starRingEnd ℂ (convPow μ K g) = convPow μ K g := by
-- proof
  induction K with
  | zero => intro g; simp only [convPow]; split_ifs with h <;> simp
  | succ n ih =>
    intro g; simp only [convPow, groupConv, map_sum, map_mul, ih, hreal]

end SelbergExpansion

namespace SelbergExpansion

/--
[convPow_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SelbergExpansion.lean)
-/
@[path]
lemma convPow_add
  [Fintype G]
  [DecidableEq G]
  [Group G]
  {μ : G → ℂ}
  {m n : ℕ} :
-- imply
  convPow μ (m + n) = groupConv (convPow μ m) (convPow μ n) := by
-- proof
  induction n with
  | zero =>
    simp only [Nat.add_zero, convPow]
    exact (groupConv_delta_right _).symm
  | succ n ih =>
    rw [show m + (n + 1) = (m + n) + 1 from by omega]
    show groupConv (convPow μ (m + n)) μ = groupConv (convPow μ m) (groupConv (convPow μ n) μ)
    rw [ih, groupConv_assoc]

end SelbergExpansion

namespace SelbergExpansion

/--
[cayleyEdgeCount_eq_card_mul_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SelbergExpansion.lean)
-/
@[path]
lemma cayleyEdgeCount_eq_card_mul_sum
  [Fintype G]
  [DecidableEq G]
  [Group G]
  {A S T : Finset G}
-- given
  (hA : A.Nonempty) :
-- imply
  (cayleyEdgeCount A S T : ℝ) = (A.card : ℝ) * (∑ s ∈ S, ∑ t ∈ T, (uniformMeasure A (s⁻¹ * t)).re) := by
-- proof
  have hAc : (A.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hA)
  have hum : ∀ g : G, (uniformMeasure A g).re =
    (if g ∈ A then (1 : ℝ) else 0) * (A.card : ℝ)⁻¹ := by
    intro g; simp only [uniformMeasure]
    split_ifs <;> simp
  simp_rw [hum]
  rw [show (A.card : ℝ) * ∑ s ∈ S, ∑ t ∈ T,
    (if s⁻¹ * t ∈ A then (1 : ℝ) else 0) * (A.card : ℝ)⁻¹ =
    ∑ s ∈ S, ∑ t ∈ T, if s⁻¹ * t ∈ A then (1 : ℝ) else 0 from by
      rw [Finset.mul_sum]
      congr 1
      ext s
      rw [Finset.mul_sum]
      congr 1
      ext t
      split_ifs <;> simp [mul_inv_cancel₀ hAc]]
  simp only [cayleyEdgeCount, Finset.card_filter, Nat.cast_sum]
  simp_rw [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [Finset.sum_product' (f := fun s t => if s⁻¹ * t ∈ A then (1 : ℝ) else 0)]

end SelbergExpansion

namespace SelbergExpansion

/--
[weighted_jensen_univ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SelbergExpansion.lean)
-/
@[path]
lemma weighted_jensen_univ
  [Fintype G]
  [DecidableEq G]
  [Group G]
  {w x : G → ℝ}
-- given
  (hw : ∀ g, 0 ≤ w g) :
-- imply
  (∑ g : G, w g * x g) ^ 2 ≤ (∑ g : G, w g) * (∑ g : G, w g * x g ^ 2) := by
-- proof
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun g => Real.sqrt (w g)) (fun g => Real.sqrt (w g) * x g)
  have h1 : ∀ g, Real.sqrt (w g) ^ 2 = w g :=
    fun g => Real.sq_sqrt (hw g)
  have h2 : ∀ g, Real.sqrt (w g) * (Real.sqrt (w g) * x g) = w g * x g := by
    intro g; rw [← mul_assoc, ← sq, h1]
  have h3 : ∀ g, (Real.sqrt (w g) * x g) ^ 2 = w g * x g ^ 2 := by
    intro g; rw [mul_pow, Real.sq_sqrt (hw g)]
  simp_rw [h1, h2, h3] at h
  simpa using h

end SelbergExpansion

namespace SelbergExpansion

/--
[l2NormSq_convOp_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SelbergExpansion.lean)
-/
@[path]
lemma l2NormSq_convOp_le
  [Fintype G]
  [DecidableEq G]
  [Group G]
  [Fintype G]
  [DecidableEq G]
  [Group G]
  {μ : G → ℂ}
  {f : G → ℂ}
-- given
  (hμ_nonneg : ∀ g, 0 ≤ (μ g).re)
  (hμ_im : ∀ g, (μ g).im = 0)
  (hμ_sum : ∑ g : G, μ g = 1) :
-- imply
  l2NormSq (convOp μ f) ≤ l2NormSq f := by
-- proof
  have hμ_re_sum : ∑ g : G, (μ g).re = 1 := by
    have h := congr_arg Complex.re hμ_sum; simpa using h
  have hμ_norm : ∀ g, ‖μ g‖ = (μ g).re := by
    intro g
    have hzeq : μ g = ((μ g).re : ℂ) := by
      apply Complex.ext
      · simp [Complex.ofReal_re]
      · simp [hμ_im g, Complex.ofReal_im]
    conv_lhs => rw [hzeq]
    rw [Complex.norm_real, Real.norm_of_nonneg (hμ_nonneg g)]
  have pointwise : ∀ g : G, ‖convOp μ f g‖ ^ 2 ≤
    ∑ g₂ : G, (μ g₂).re * ‖f (g * g₂⁻¹)‖ ^ 2 := by
    intro g
    have eq1 : convOp μ f g = ∑ g₂ : G, μ g₂ * f (g * g₂⁻¹) := by
      show ∑ g₁ : G, f g₁ * μ (g₁⁻¹ * g) = _
      rw [show (∑ g₁ : G, f g₁ * μ (g₁⁻¹ * g)) =
        ∑ h : G, f (g * h⁻¹) * μ h from by
        refine (Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulLeft g)) _ _ ?_).symm
        intro h; simp only [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulLeft]
        congr 1; congr 1; group]
      congr 1; ext g₂; ring
    rw [eq1]
    calc ‖∑ g₂ : G, μ g₂ * f (g * g₂⁻¹)‖ ^ 2
      ≤ (∑ g₂ : G, ‖μ g₂ * f (g * g₂⁻¹)‖) ^ 2 := by
        gcongr; exact norm_sum_le _ _
      _ = (∑ g₂ : G, (μ g₂).re * ‖f (g * g₂⁻¹)‖) ^ 2 := by
        congr 1
        apply Finset.sum_congr rfl
        intro g₂ _; rw [norm_mul, hμ_norm]
      _ ≤ (∑ g₂ : G, (μ g₂).re) * (∑ g₂ : G, (μ g₂).re * ‖f (g * g₂⁻¹)‖ ^ 2) :=
        weighted_jensen_univ (fun g₂ => (μ g₂).re) (fun g₂ => ‖f (g * g₂⁻¹)‖) hμ_nonneg
      _ = ∑ g₂ : G, (μ g₂).re * ‖f (g * g₂⁻¹)‖ ^ 2 := by
        rw [hμ_re_sum, one_mul]
  calc l2NormSq (convOp μ f)
    = ∑ g : G, ‖convOp μ f g‖ ^ 2 := rfl
    _ ≤ ∑ g : G, ∑ g₂ : G, (μ g₂).re * ‖f (g * g₂⁻¹)‖ ^ 2 :=
      Finset.sum_le_sum (fun g _ => pointwise g)
    _ = ∑ g₂ : G, ∑ g : G, (μ g₂).re * ‖f (g * g₂⁻¹)‖ ^ 2 := by
      rw [Finset.sum_comm]
    _ = ∑ g₂ : G, (μ g₂).re * ∑ g : G, ‖f (g * g₂⁻¹)‖ ^ 2 := by
      apply Finset.sum_congr rfl; intro g₂ _; rw [Finset.mul_sum]
    _ = ∑ g₂ : G, (μ g₂).re * l2NormSq f := by
      apply Finset.sum_congr rfl; intro g₂ _; congr 1
      exact Fintype.sum_equiv (Equiv.mulRight g₂⁻¹) _ _ (fun g => rfl)
    _ = (∑ g₂ : G, (μ g₂).re) * l2NormSq f := by
      rw [Finset.sum_mul]
    _ = l2NormSq f := by
      rw [hμ_re_sum, one_mul]

end SelbergExpansion

namespace SelbergExpansion

/--
[l2NormSq_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SelbergExpansion.lean)
-/
@[path]
lemma l2NormSq_nonneg
  [Fintype G]
  [DecidableEq G]
  [Group G]
  {f : G → ℂ} :
-- imply
  0 ≤ l2NormSq f := by
-- proof
  apply Finset.sum_nonneg
  intro g _
  positivity

end SelbergExpansion

namespace SelbergExpansion

/--
[symmetric_l2_norm_eq_identity_eval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SelbergExpansion.lean)
-/
@[path]
lemma symmetric_l2_norm_eq_identity_eval
  [Fintype G]
  [DecidableEq G]
  [Group G]
  {μ : G → ℂ}
  {K : ℕ}
-- given
  (hμ : IsSymmetricMeasure μ)
  (hreal : ∀ g, starRingEnd ℂ (μ g) = μ g) :
-- imply
  (l2NormSq (convPow μ K) : ℂ) = convPow μ (2 * K) 1 := by
-- proof
  have hsym := convPow_symmetric μ hμ K
  have hconj := convPow_conj μ hreal K
  have key : (l2NormSq (convPow μ K) : ℂ) = groupConv (convPow μ K) (convPow μ K) 1 := by
    simp only [l2NormSq, groupConv, mul_one]
    push_cast
    congr 1; ext g
    rw [← hsym g]
    rw [show (↑‖convPow μ K g‖ : ℂ) ^ 2 = (↑(‖convPow μ K g‖ ^ 2) : ℂ) from by
      push_cast; ring]
    rw [Complex.sq_norm]
    rw [show (↑(Complex.normSq (convPow μ K g)) : ℂ) =
      convPow μ K g * starRingEnd ℂ (convPow μ K g) from (Complex.mul_conj _).symm]
    rw [hconj g]
  rw [key, show 2 * K = K + K from by ring, convPow_add]

end SelbergExpansion

namespace SelbergExpansion

/--
[l2NormSq_nonneg'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SelbergExpansion.lean)
-/
@[path]
lemma l2NormSq_nonneg'
  [Fintype G]
  {f : G → ℂ} :
-- imply
  0 ≤ l2NormSq f :=
-- proof
  Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 2)

end SelbergExpansion

namespace SelbergExpansion

/--
[l2NormSq_pos_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SelbergExpansion.lean)
-/
@[path]
lemma l2NormSq_pos_of_ne
  [Fintype G]
  {f : G → ℂ}
-- given
  (h : l2NormSq f ≠ 0) :
-- imply
  0 < l2NormSq f :=
-- proof
  lt_of_le_of_ne (l2NormSq_nonneg' f) (Ne.symm h)

end SelbergExpansion

namespace SelbergExpansion

/--
[sqrt_div_le_sqrt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SelbergExpansion.lean)
-/
@[path]
lemma sqrt_div_le_sqrt
  {A B C : ℝ}
-- given
  (hB : 0 < B)
  (hC : 0 ≤ C)
  (h : A ≤ C * B) :
-- imply
  Real.sqrt A / Real.sqrt B ≤ Real.sqrt C := by
-- proof
  rw [div_le_iff₀ (Real.sqrt_pos.mpr hB), ← Real.sqrt_mul hC]
  exact Real.sqrt_le_sqrt h

end SelbergExpansion

namespace SelbergExpansion

/--
[sigma1_sq_le_of_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SelbergExpansion.lean)
-/
@[path]
lemma sigma1_sq_le_of_bound
  [Fintype G]
  [DecidableEq G]
  [Group G]
  {μ : G → ℂ}
  {B : ℝ}
-- given
  (hB : 0 ≤ B)
  (hbdd : ∀ f : G → ℂ, IsMeanZero f → l2NormSq f ≠ 0 → l2NormSq (convOp μ f) ≤ B * l2NormSq f) :
-- imply
  sigma1 μ ^ 2 ≤ B := by
-- proof
  have helem : ∀ r ∈ {r : ℝ | ∃ f : G → ℂ, IsMeanZero f ∧ l2NormSq f ≠ 0 ∧
    r = Real.sqrt (l2NormSq (convOp μ f)) / Real.sqrt (l2NormSq f)},
    r ≤ Real.sqrt B := by
    intro r ⟨f, hfm, hfn, hr⟩
    rw [hr]
    exact sqrt_div_le_sqrt (l2NormSq_pos_of_ne hfn) hB (hbdd f hfm hfn)
  have helem_nn : ∀ r ∈ {r : ℝ | ∃ f : G → ℂ, IsMeanZero f ∧ l2NormSq f ≠ 0 ∧
    r = Real.sqrt (l2NormSq (convOp μ f)) / Real.sqrt (l2NormSq f)}, 0 ≤ r := by
    intro r ⟨_, _, _, hr⟩; rw [hr]; exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsup_le : sigma1 μ ≤ Real.sqrt B := by
    unfold sigma1
    by_cases hne : (∃ r, r ∈ {r : ℝ | ∃ f : G → ℂ, IsMeanZero f ∧ l2NormSq f ≠ 0 ∧
      r = Real.sqrt (l2NormSq (convOp μ f)) / Real.sqrt (l2NormSq f)})
    · exact csSup_le ⟨_, hne.choose_spec⟩ helem
    · push Not at hne
      have hempty : {r : ℝ | ∃ f : G → ℂ, IsMeanZero f ∧ l2NormSq f ≠ 0 ∧
        r = Real.sqrt (l2NormSq (convOp μ f)) / Real.sqrt (l2NormSq f)} = ∅ := by
        ext x; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]; exact hne x
      rw [hempty, Real.sSup_empty]
      exact Real.sqrt_nonneg _
  have hsup_nn : 0 ≤ sigma1 μ := by
    unfold sigma1
    by_cases hne : (∃ r, r ∈ {r : ℝ | ∃ f : G → ℂ, IsMeanZero f ∧ l2NormSq f ≠ 0 ∧
      r = Real.sqrt (l2NormSq (convOp μ f)) / Real.sqrt (l2NormSq f)})
    · exact le_csSup_of_le ⟨Real.sqrt B, helem⟩ hne.choose_spec (helem_nn _ hne.choose_spec)
    · push Not at hne
      have hempty : {r : ℝ | ∃ f : G → ℂ, IsMeanZero f ∧ l2NormSq f ≠ 0 ∧
        r = Real.sqrt (l2NormSq (convOp μ f)) / Real.sqrt (l2NormSq f)} = ∅ := by
        ext x; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]; exact hne x
      rw [hempty, Real.sSup_empty]
  nlinarith [Real.sq_sqrt hB]

end SelbergExpansion

namespace SelbergExpansion

/--
[sl2ZBall_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SelbergExpansion.lean)
-/
@[path]
lemma sl2ZBall_finite
  {T : ℝ} :
-- imply
  Set.Finite (sl2ZBall T) := by
-- proof
  let N := ⌊T ^ 2⌋
  let f : SpecialLinearGroup (Fin 2) ℤ → ℤ × ℤ × ℤ × ℤ := fun g =>
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0,
      (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1,
      (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0,
      (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1)
  let S : Set (ℤ × ℤ × ℤ × ℤ) :=
    (Set.Icc (-N) N) ×ˢ ((Set.Icc (-N) N) ×ˢ ((Set.Icc (-N) N) ×ˢ (Set.Icc (-N) N)))
  apply Set.Finite.of_injOn (f := f) (t := S)
  · intro g hg
    simp only [sl2ZBall, Set.mem_setOf_eq] at hg
    simp only [S, f, Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;>
    nlinarith [sq_nonneg ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0),
      sq_nonneg ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 1),
      sq_nonneg ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0),
      sq_nonneg ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1)]
  · intro g₁ _ g₂ _ heq
    simp only [f, Prod.mk.injEq] at heq
    ext i j
    fin_cases i <;> fin_cases j <;>
      [exact heq.1; exact heq.2.1; exact heq.2.2.1; exact heq.2.2.2]
  · exact (Set.finite_Icc _ _).prod
    ((Set.finite_Icc _ _).prod ((Set.finite_Icc _ _).prod (Set.finite_Icc _ _)))
/-- The cardinality of `sl2ZBall T` grows like `T²`: there exist `c, C > 0` such
that `c·T² ≤ |sl2ZBall T| ≤ C·T²` for all `T ≥ 2`. -/

end SelbergExpansion


-- created on 2026-10-23
