import Mathlib.MeasureTheory.Group.Measure

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory.ContractionDecay

section Shells

variable {G : Type*}

def shell (S : Set G) (φ : G → ℝ) (c r : ℝ) (k : ℕ) : Set G :=
  S ∩ φ ⁻¹' Ico (r ^ k * c) (r ^ (k + 1) * c)

theorem shell_zero_eq (S : Set G) (φ : G → ℝ) {c : ℝ} (r : ℝ) (hSc : ∀ g ∈ S, c ≤ φ g) :
    shell S φ c r 0 = S ∩ φ ⁻¹' Iio (r * c) := by
  ext g
  simp only [shell, pow_zero, one_mul, zero_add, pow_one, mem_inter_iff, mem_preimage, mem_Ico,
    mem_Iio]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hSc g h.1, h.2⟩⟩

theorem iUnion_shell {S : Set G} {φ : G → ℝ} {c r : ℝ} (hc : 0 < c) (hr : 1 < r)
    (hSc : ∀ g ∈ S, c ≤ φ g) : ⋃ k, shell S φ c r k = S := by
  ext g
  simp only [mem_iUnion, shell, mem_inter_iff, mem_preimage, mem_Ico]
  constructor
  · rintro ⟨k, hk, -⟩
    exact hk
  · intro hg
    obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near ((one_le_div hc).mpr (hSc g hg)) hr
    exact ⟨k, hg, (le_div_iff₀ hc).mp hk1, (div_lt_iff₀ hc).mp hk2⟩

theorem pairwise_disjoint_shell (S : Set G) (φ : G → ℝ) {c r : ℝ} (hc : 0 < c) (hr : 1 < r) :
    Pairwise (Function.onFun Disjoint (shell S φ c r)) := by
  intro k l hkl
  rw [Function.onFun, Set.disjoint_left]
  rintro g ⟨-, hk1, hk2⟩ ⟨-, hl1, hl2⟩
  rcases Nat.lt_or_gt_of_ne hkl with h | h
  · have : r ^ (k + 1) * c ≤ r ^ l * c :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hr.le h) hc.le
    exact lt_irrefl _ (hk2.trans_le (this.trans hl1))
  · have : r ^ (l + 1) * c ≤ r ^ k * c :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hr.le h) hc.le
    exact lt_irrefl _ (hl2.trans_le (this.trans hk1))

theorem measurableSet_shell [MeasurableSpace G] {S : Set G} (hS : MeasurableSet S) {φ : G → ℝ}
    (hφ : Measurable φ) (c r : ℝ) (k : ℕ) : MeasurableSet (shell S φ c r k) :=
  hS.inter (hφ measurableSet_Ico)

theorem mul_le_of_mem_shell_succ {S : Set G} {φ : G → ℝ} {c r : ℝ} (hc : 0 < c) (hr : 1 < r)
    {k : ℕ} {g : G} (hg : g ∈ shell S φ c r (k + 1)) : r * c ≤ φ g := by
  obtain ⟨-, hk1, -⟩ := hg
  refine le_trans ?_ hk1
  calc r * c = r ^ 1 * c := by rw [pow_one]
    _ ≤ r ^ (k + 1) * c := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hr.le (by omega)) hc.le

end Shells

section Decay

variable {G : Type*} [Group G]

theorem image_mul_shell_succ_subset {S : Set G} {φ : G → ℝ} {c r : ℝ} (hc : 0 < c) (hr : 1 < r)
    {p : G} (hp : ∀ g ∈ S, r * c ≤ φ g → p * g ∈ S ∧ φ (p * g) = φ g / r) (k : ℕ) :
    (fun g => p * g) '' shell S φ c r (k + 1) ⊆ shell S φ c r k := by
  rintro _ ⟨g, hg, rfl⟩
  have hr0 : 0 < r := one_pos.trans hr
  obtain ⟨hpS, hφp⟩ := hp g hg.1 (mul_le_of_mem_shell_succ hc hr hg)
  obtain ⟨-, hk1, hk2⟩ := hg
  refine ⟨hpS, ?_, ?_⟩
  · show r ^ k * c ≤ φ (p * g)
    rw [hφp, le_div_iff₀ hr0]
    calc r ^ k * c * r = r ^ (k + 1) * c := by ring
      _ ≤ φ g := hk1
  · show φ (p * g) < r ^ (k + 1) * c
    rw [hφp, div_lt_iff₀ hr0]
    calc φ g < r ^ (k + 1 + 1) * c := hk2
      _ = r ^ (k + 1) * c * r := by ring

variable [MeasurableSpace G] [MeasurableMul G]

theorem two_mul_measure_shell_succ_le (μ : Measure G) [μ.IsMulLeftInvariant] {S : Set G}
    (hS : MeasurableSet S) {φ : G → ℝ} (hφ : Measurable φ) {c r : ℝ} (hc : 0 < c) (hr : 1 < r)
    {p q : G} (hp : ∀ g ∈ S, r * c ≤ φ g → p * g ∈ S ∧ φ (p * g) = φ g / r)
    (hq : ∀ g ∈ S, r * c ≤ φ g → q * g ∈ S ∧ φ (q * g) = φ g / r)
    (hpq : ∀ g ∈ S, ∀ g' ∈ S, r * c ≤ φ g → r * c ≤ φ g' → p * g ≠ q * g') (k : ℕ) :
    2 * μ (shell S φ c r (k + 1)) ≤ μ (shell S φ c r k) := by
  set T := shell S φ c r (k + 1) with hT_def
  have hT : MeasurableSet T := measurableSet_shell hS hφ c r (k + 1)
  have hmeas : ∀ a : G, MeasurableSet ((fun g => a * g) '' T) := fun a => by
    rw [image_mul_left]
    exact measurable_const_mul _ hT
  have hμ : ∀ a : G, μ ((fun g => a * g) '' T) = μ T := fun a => by
    rw [image_mul_left, measure_preimage_mul]
  have hdisj : Disjoint ((fun g => p * g) '' T) ((fun g => q * g) '' T) := by
    rw [Set.disjoint_left]
    rintro _ ⟨g, hg, rfl⟩ ⟨g', hg', he⟩
    exact hpq g hg.1 g' hg'.1 (mul_le_of_mem_shell_succ hc hr hg)
      (mul_le_of_mem_shell_succ hc hr hg') he.symm
  calc 2 * μ T = μ ((fun g => p * g) '' T) + μ ((fun g => q * g) '' T) := by rw [hμ, hμ, two_mul]
    _ = μ ((fun g => p * g) '' T ∪ (fun g => q * g) '' T) := (measure_union hdisj (hmeas q)).symm
    _ ≤ μ (shell S φ c r k) := measure_mono (union_subset
        (image_mul_shell_succ_subset hc hr hp k) (image_mul_shell_succ_subset hc hr hq k))

theorem measure_shell_le (μ : Measure G) [μ.IsMulLeftInvariant] {S : Set G}
    (hS : MeasurableSet S) {φ : G → ℝ} (hφ : Measurable φ) {c r : ℝ} (hc : 0 < c) (hr : 1 < r)
    {p q : G} (hp : ∀ g ∈ S, r * c ≤ φ g → p * g ∈ S ∧ φ (p * g) = φ g / r)
    (hq : ∀ g ∈ S, r * c ≤ φ g → q * g ∈ S ∧ φ (q * g) = φ g / r)
    (hpq : ∀ g ∈ S, ∀ g' ∈ S, r * c ≤ φ g → r * c ≤ φ g' → p * g ≠ q * g') (k : ℕ) :
    μ (shell S φ c r k) ≤ 2⁻¹ ^ k * μ (shell S φ c r 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc μ (shell S φ c r (k + 1)) = 2⁻¹ * (2 * μ (shell S φ c r (k + 1))) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
      _ ≤ 2⁻¹ * μ (shell S φ c r k) :=
          mul_le_mul_right (two_mul_measure_shell_succ_le μ hS hφ hc hr hp hq hpq k) _
      _ ≤ 2⁻¹ * (2⁻¹ ^ k * μ (shell S φ c r 0)) := mul_le_mul_right ih _
      _ = 2⁻¹ ^ (k + 1) * μ (shell S φ c r 0) := by rw [← mul_assoc, pow_succ']

theorem measure_le_two_mul_measure_inter (μ : Measure G) [μ.IsMulLeftInvariant] {S : Set G}
    (hS : MeasurableSet S) {φ : G → ℝ} (hφ : Measurable φ) {c r : ℝ} (hc : 0 < c) (hr : 1 < r)
    (hSc : ∀ g ∈ S, c ≤ φ g)
    {p q : G} (hp : ∀ g ∈ S, r * c ≤ φ g → p * g ∈ S ∧ φ (p * g) = φ g / r)
    (hq : ∀ g ∈ S, r * c ≤ φ g → q * g ∈ S ∧ φ (q * g) = φ g / r)
    (hpq : ∀ g ∈ S, ∀ g' ∈ S, r * c ≤ φ g → r * c ≤ φ g' → p * g ≠ q * g') :
    μ S ≤ 2 * μ (S ∩ φ ⁻¹' Iio (r * c)) := by
  calc μ S = μ (⋃ k, shell S φ c r k) := by rw [iUnion_shell hc hr hSc]
    _ = ∑' k, μ (shell S φ c r k) :=
        measure_iUnion (pairwise_disjoint_shell S φ hc hr) (measurableSet_shell hS hφ c r)
    _ ≤ ∑' k, 2⁻¹ ^ k * μ (shell S φ c r 0) :=
        ENNReal.tsum_le_tsum (measure_shell_le μ hS hφ hc hr hp hq hpq)
    _ = (∑' k, (2⁻¹ : ℝ≥0∞) ^ k) * μ (shell S φ c r 0) := ENNReal.tsum_mul_right
    _ = 2 * μ (S ∩ φ ⁻¹' Iio (r * c)) := by
        rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv, shell_zero_eq S φ r hSc]

theorem measure_lt_top_of_measure_inter_lt_top (μ : Measure G) [μ.IsMulLeftInvariant]
    {S : Set G} (hS : MeasurableSet S) {φ : G → ℝ} (hφ : Measurable φ) {c r : ℝ} (hc : 0 < c)
    (hr : 1 < r) (hSc : ∀ g ∈ S, c ≤ φ g)
    {p q : G} (hp : ∀ g ∈ S, r * c ≤ φ g → p * g ∈ S ∧ φ (p * g) = φ g / r)
    (hq : ∀ g ∈ S, r * c ≤ φ g → q * g ∈ S ∧ φ (q * g) = φ g / r)
    (hpq : ∀ g ∈ S, ∀ g' ∈ S, r * c ≤ φ g → r * c ≤ φ g' → p * g ≠ q * g')
    (hfin : μ (S ∩ φ ⁻¹' Iio (r * c)) < ⊤) : μ S < ⊤ :=
  (measure_le_two_mul_measure_inter μ hS hφ hc hr hSc hp hq hpq).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofNat_lt_top hfin)

end Decay

end MeasureTheory.ContractionDecay
