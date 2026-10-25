/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Analysis.NormedSpace.GrothendieckInequality.Part5
open scoped InnerProductSpace


section

namespace FunctionalAnalysis.GrothendieckInequalityWanted

-- N11a
theorem fullV_eq {d : ℕ} (X : EuclideanSpace ℝ (Fin d)) :
    fullV X = lowV X + highV X := by
  change scaledVec (radEmbed X) = scaledVec _ + scaledVec _
  rw [← scaledVec_add]
  congr 1
  funext ω
  change radEmbed X ω
    = truncAt 8 (radEmbed X ω) + (radEmbed X ω - truncAt 8 (radEmbed X ω))
  exact Eq.symm (add_sub_cancel (truncAt 8 (radEmbed X ω)) (radEmbed X ω))

-- N11b
theorem fullV_inner {d : ℕ} (X Y : EuclideanSpace ℝ (Fin d)) :
    ⟪fullV X, fullV Y⟫_ℝ = ⟪X, Y⟫_ℝ := by
  change ⟪scaledVec (radEmbed X), scaledVec (radEmbed Y)⟫_ℝ = _
  rw [scaledVec_inner, radEmbed_moment_a]
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (2:ℝ)^d ≠ 0), one_mul]

-- N11c
theorem fullV_norm_le {d : ℕ} (X : EuclideanSpace ℝ (Fin d)) (hX : ‖X‖ ≤ 1) :
    ‖fullV X‖ ≤ 1 := by
  change ‖scaledVec (radEmbed X)‖ ≤ 1
  apply scaledVec_norm_le _ (by norm_num)
  have h2 := radEmbed_moment_b (d := d) X
  have h12 : ‖X‖^2 ≤ 1 := by nlinarith [norm_nonneg X, hX]
  calc ((2:ℝ)^d)⁻¹ * ∑ ω, (radEmbed X ω)^2
        = ((2:ℝ)^d)⁻¹ * ((2:ℝ)^d * ‖X‖^2) := by rw [h2]
      _ = ‖X‖^2 := by
          rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (2:ℝ)^d ≠ 0), one_mul]
      _ ≤ 1 := h12
      _ = 1^2 := (one_pow 2).symm

-- N11d
theorem lowV_norm_le {d : ℕ} (X : EuclideanSpace ℝ (Fin d)) (hX : ‖X‖ ≤ 1) :
    ‖lowV X‖ ≤ 1 := by
  change ‖scaledVec (fun ω => truncAt 8 (radEmbed X ω))‖ ≤ 1
  apply scaledVec_norm_le _ (by norm_num)
  have h2 := radEmbed_moment_b (d := d) X
  have hle : (∑ ω, (truncAt 8 (radEmbed X ω))^2) ≤ ∑ ω, (radEmbed X ω)^2 := by
    apply Finset.sum_le_sum
    intro ω _
    exact (truncAt_facts (show (0:ℝ) < 8 by norm_num)).2.1
  have h12 : ‖X‖^2 ≤ 1 := by nlinarith [norm_nonneg X, hX]
  calc ((2:ℝ)^d)⁻¹ * ∑ ω, (truncAt 8 (radEmbed X ω))^2
        ≤ ((2:ℝ)^d)⁻¹ * ∑ ω, (radEmbed X ω)^2 :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = ((2:ℝ)^d)⁻¹ * ((2:ℝ)^d * ‖X‖^2) := by rw [h2]
      _ = ‖X‖^2 := by
          rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (2:ℝ)^d ≠ 0), one_mul]
      _ ≤ 1 := h12
      _ = 1^2 := (one_pow 2).symm

-- N11e
theorem highV_norm_le {d : ℕ} (X : EuclideanSpace ℝ (Fin d)) (hX : ‖X‖ ≤ 1) :
    ‖highV X‖ ≤ 1/4 := by
  change ‖scaledVec (fun ω => radEmbed X ω - truncAt 8 (radEmbed X ω))‖ ≤ 1/4
  apply scaledVec_norm_le _ (by norm_num)
  have h4 := radEmbed_moment_c (d := d) X
  have htail : ∀ ω : Fin d → Bool,
      (radEmbed X ω - truncAt 8 (radEmbed X ω))^2 ≤ (radEmbed X ω)^4 / 64 := by
    intro ω
    have h := (truncAt_facts (show (0:ℝ) < 8 by norm_num)
      (t := radEmbed X ω)).2.2
    have h64 : (8:ℝ)^2 = 64 := by norm_num
    rw [h64] at h
    exact (le_div_iff₀ (show (0:ℝ) < 64 by norm_num)).mpr h
  have hsum : (∑ ω : Fin d → Bool, (radEmbed X ω - truncAt 8 (radEmbed X ω))^2)
      ≤ (∑ ω : Fin d → Bool, (radEmbed X ω)^4) / 64 := by
    calc (∑ ω : Fin d → Bool, (radEmbed X ω - truncAt 8 (radEmbed X ω))^2)
          ≤ ∑ ω : Fin d → Bool, ((radEmbed X ω)^4 / 64) :=
            Finset.sum_le_sum (fun ω _ => htail ω)
        _ = (∑ ω : Fin d → Bool, (radEmbed X ω)^4) / 64 :=
            (Finset.sum_div _ _ _).symm
  have h12 : ‖X‖^2 ≤ 1 := by nlinarith [norm_nonneg X, hX]
  have h14 : ‖X‖^4 ≤ 1 := by
    have e : ‖X‖^4 = (‖X‖^2)^2 := by ring
    rw [e]
    calc (‖X‖^2)^2 ≤ 1^2 := pow_le_pow_left₀ (sq_nonneg _) h12 2
      _ = 1 := one_pow 2
  have h4cancel : ((2:ℝ)^d)⁻¹ * ((3 * (2:ℝ)^d * ‖X‖^4) / 64) = 3 * ‖X‖^4 / 64 := by
    calc ((2:ℝ)^d)⁻¹ * ((3 * (2:ℝ)^d * ‖X‖^4) / 64)
          = (((2:ℝ)^d)⁻¹ * (2:ℝ)^d) * (3 * ‖X‖^4 / 64) := by ring
        _ = 3 * ‖X‖^4 / 64 := by
            rw [inv_mul_cancel₀ (by positivity : (2:ℝ)^d ≠ 0), one_mul]
  calc ((2:ℝ)^d)⁻¹ * ∑ ω, (radEmbed X ω - truncAt 8 (radEmbed X ω))^2
        ≤ ((2:ℝ)^d)⁻¹ * ((∑ ω, (radEmbed X ω)^4) / 64) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ ((2:ℝ)^d)⁻¹ * ((3 * (2:ℝ)^d * ‖X‖^4) / 64) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hdiv : (∑ ω, (radEmbed X ω)^4) * (64:ℝ)⁻¹
              ≤ (3 * (2:ℝ)^d * ‖X‖^4) * 64⁻¹ :=
            mul_le_mul_of_nonneg_right h4 (by positivity)
          simpa [div_eq_mul_inv] using hdiv
      _ = 3 * ‖X‖^4 / 64 := h4cancel
      _ ≤ 3 * 1 / 64 := by
          have hdiv : (3 * ‖X‖^4) * (64:ℝ)⁻¹ ≤ (3 * 1) * 64⁻¹ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h14 (by norm_num)) (by positivity)
          simpa [div_eq_mul_inv] using hdiv
      _ ≤ (1/4)^2 := by norm_num

-- N12-N15 (part7)
-- N12: low part bounded by sign maximum
theorem low_part_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) {β : ℝ}
    (hsign : ∀ (ε : Fin m → ℝ) (δ : Fin n → ℝ),
      (∀ i, ε i = 1 ∨ ε i = -1) → (∀ j, δ j = 1 ∨ δ j = -1) →
      |∑ i : Fin m, ∑ j : Fin n, A i j * ε i * δ j| ≤ β)
    {d : ℕ} (X : Fin m → EuclideanSpace ℝ (Fin d))
    (Y : Fin n → EuclideanSpace ℝ (Fin d)) :
    |∑ i, ∑ j, A i j * ⟪lowV (X i), lowV (Y j)⟫_ℝ| ≤ 64 * β := by
  have efunds : ∀ i j, ⟪lowV (X i), lowV (Y j)⟫_ℝ
      = ((2:ℝ)^d)⁻¹ * ∑ ω, truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω) := by
    intro i j
    change ⟪scaledVec _, scaledVec _⟫_ℝ = _
    rw [scaledVec_inner]
  have step1 : ∀ i j, A i j * ⟪lowV (X i), lowV (Y j)⟫_ℝ
      = ((2:ℝ)^d)⁻¹ * (∑ ω,
          A i j * truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω)) := by
    intro i j
    have e1 : A i j * ⟪lowV (X i), lowV (Y j)⟫_ℝ
        = ((2:ℝ)^d)⁻¹ * (A i j * (∑ ω,
            truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω))) := by
      rw [efunds i j]; ring
    have e2 : A i j * (∑ ω, truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω))
        = ∑ ω, A i j * truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      exact (mul_assoc _ _ _).symm
    rw [e1, e2]
  have esum : (∑ i, ∑ j, A i j * ⟪lowV (X i), lowV (Y j)⟫_ℝ)
      = ((2:ℝ)^d)⁻¹ * ∑ ω : Fin d → Bool, (∑ i, ∑ j,
        A i j * truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω)) := by
    calc (∑ i, ∑ j, A i j * ⟪lowV (X i), lowV (Y j)⟫_ℝ)
          = ∑ i, ∑ j, ((2:ℝ)^d)⁻¹ * (∑ ω,
              A i j * truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω)) :=
            Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => step1 i j))
        _ = ∑ i, ∑ j, ∑ ω : Fin d → Bool, ((2:ℝ)^d)⁻¹ *
            (A i j * truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω)) := by
            simp only [Finset.mul_sum]
        _ = ∑ ω : Fin d → Bool, ∑ i, ∑ j, ((2:ℝ)^d)⁻¹ *
            (A i j * truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω)) := by
            calc (∑ i, ∑ j, ∑ ω : Fin d → Bool, ((2:ℝ)^d)⁻¹ *
                    (A i j * truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω)))
                  = ∑ i, ∑ ω : Fin d → Bool, ∑ j, ((2:ℝ)^d)⁻¹ *
                    (A i j * truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω)) := by
                    apply Finset.sum_congr rfl; intro i _
                    exact Finset.sum_comm
                _ = ∑ ω : Fin d → Bool, ∑ i, ∑ j, ((2:ℝ)^d)⁻¹ *
                    (A i j * truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω)) :=
                    Finset.sum_comm
        _ = ((2:ℝ)^d)⁻¹ * ∑ ω : Fin d → Bool, (∑ i, ∑ j,
            A i j * truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω)) := by
            simp only [← Finset.mul_sum]
  have hF : ∀ ω : Fin d → Bool,
      |∑ i, ∑ j, A i j * truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω)|
        ≤ 64 * β := by
    intro ω
    have h1 := abs_bilinear_le_sq_mul_of_sign_bound (m := m) (n := n) A (M := 8) (β := β)
      (by norm_num) hsign
      (fun i => truncAt 8 (radEmbed (X i) ω)) (fun j => truncAt 8 (radEmbed (Y j) ω))
      (fun i => (truncAt_facts (show (0:ℝ) < 8 by norm_num)).1)
      (fun j => (truncAt_facts (show (0:ℝ) < 8 by norm_num)).1)
    have e : (8:ℝ)^2 * β = 64 * β := by ring
    rwa [e] at h1
  have hpos : (0:ℝ) ≤ ((2:ℝ)^d)⁻¹ := by positivity
  have hcard : (0:ℝ) < ((2:ℝ)^d) := by positivity
  calc |∑ i, ∑ j, A i j * ⟪lowV (X i), lowV (Y j)⟫_ℝ|
        = |((2:ℝ)^d)⁻¹ * ∑ ω : Fin d → Bool, (∑ i, ∑ j,
          A i j * truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω))| := by
          rw [esum]
      _ = ((2:ℝ)^d)⁻¹ * |∑ ω : Fin d → Bool, (∑ i, ∑ j,
          A i j * truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω))| := by
          rw [abs_mul, abs_of_nonneg hpos]
      _ ≤ ((2:ℝ)^d)⁻¹ * (Fintype.card (Fin d → Bool) * (64 * β)) := by
          apply mul_le_mul_of_nonneg_left _ hpos
          calc |∑ ω : Fin d → Bool, (∑ i, ∑ j,
                  A i j * truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω))|
                ≤ ∑ ω : Fin d → Bool, |∑ i, ∑ j,
                  A i j * truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω)| :=
                  Finset.abs_sum_le_sum_abs _ Finset.univ
              _ ≤ ∑ _ω : Fin d → Bool, (64 * β) :=
                  Finset.sum_le_sum (fun ω _ => hF ω)
              _ = Fintype.card (Fin d → Bool) * (64 * β) := by
                  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = 64 * β := by
          rw [card_cube, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcard), one_mul]

-- N13
theorem euclidean_self_improving_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) {β : ℝ}
    (hsign : ∀ (ε : Fin m → ℝ) (δ : Fin n → ℝ),
      (∀ i, ε i = 1 ∨ ε i = -1) → (∀ j, δ j = 1 ∨ δ j = -1) →
      |∑ i : Fin m, ∑ j : Fin n, A i j * ε i * δ j| ≤ β)
    {d : ℕ} (X : Fin m → EuclideanSpace ℝ (Fin d))
    (Y : Fin n → EuclideanSpace ℝ (Fin d))
    (hX : ∀ i, ‖X i‖ ≤ 1) (hY : ∀ j, ‖Y j‖ ≤ 1) :
    |∑ i, ∑ j, A i j * ⟪X i, Y j⟫_ℝ| ≤ 64 * β + gtBound A / 2 := by
  have e1 : ∀ i j, ⟪X i, Y j⟫_ℝ
      = ⟪lowV (X i), lowV (Y j)⟫_ℝ + ⟪highV (X i), fullV (Y j)⟫_ℝ
        + ⟪lowV (X i), highV (Y j)⟫_ℝ := by
    intro i j
    have hfull : ⟪X i, Y j⟫_ℝ = ⟪fullV (X i), fullV (Y j)⟫_ℝ := (fullV_inner _ _).symm
    rw [hfull, fullV_eq (X i), fullV_eq (Y j), inner_add_left, inner_add_right,
      ← fullV_eq (Y j)]
    ring
  have per : ∀ i j, A i j * ⟪X i, Y j⟫_ℝ
      = (A i j * ⟪lowV (X i), lowV (Y j)⟫_ℝ)
        + (A i j * ⟪highV (X i), fullV (Y j)⟫_ℝ)
        + (A i j * ⟪lowV (X i), highV (Y j)⟫_ℝ) := by
    intro i j
    rw [e1 i j]; ring
  have hsplit : (∑ i, ∑ j, A i j * ⟪X i, Y j⟫_ℝ)
      = (∑ i, ∑ j, A i j * ⟪lowV (X i), lowV (Y j)⟫_ℝ)
        + (∑ i, ∑ j, A i j * ⟪highV (X i), fullV (Y j)⟫_ℝ)
        + (∑ i, ∑ j, A i j * ⟪lowV (X i), highV (Y j)⟫_ℝ) := by
    calc (∑ i, ∑ j, A i j * ⟪X i, Y j⟫_ℝ)
          = ∑ i, ∑ j, ((A i j * ⟪lowV (X i), lowV (Y j)⟫_ℝ)
            + (A i j * ⟪highV (X i), fullV (Y j)⟫_ℝ)
            + (A i j * ⟪lowV (X i), highV (Y j)⟫_ℝ)) :=
              Finset.sum_congr rfl
                (fun i _ => Finset.sum_congr rfl (fun j _ => per i j))
        _ = _ := by simp only [Finset.sum_add_distrib]
  have hS1 : |∑ i, ∑ j, A i j * ⟪lowV (X i), lowV (Y j)⟫_ℝ| ≤ 64 * β :=
    low_part_bound A hsign X Y
  have hS2 : |∑ i, ∑ j, A i j * ⟪highV (X i), fullV (Y j)⟫_ℝ|
      ≤ gtBound A * (1/4) * 1 := by
    apply abs_sum_inner_le_gtBound_mul A (by norm_num) (by norm_num)
    · intro i
      exact highV_norm_le _ (hX i)
    · intro j
      exact fullV_norm_le _ (hY j)
  have hS3 : |∑ i, ∑ j, A i j * ⟪lowV (X i), highV (Y j)⟫_ℝ|
      ≤ gtBound A * 1 * (1/4) := by
    apply abs_sum_inner_le_gtBound_mul A (by norm_num) (by norm_num)
    · intro i
      exact lowV_norm_le _ (hX i)
    · intro j
      exact highV_norm_le _ (hY j)
  rw [hsplit]
  calc |(∑ i, ∑ j, A i j * ⟪lowV (X i), lowV (Y j)⟫_ℝ)
        + (∑ i, ∑ j, A i j * ⟪highV (X i), fullV (Y j)⟫_ℝ)
        + (∑ i, ∑ j, A i j * ⟪lowV (X i), highV (Y j)⟫_ℝ)|
        ≤ |(∑ i, ∑ j, A i j * ⟪lowV (X i), lowV (Y j)⟫_ℝ)|
          + |(∑ i, ∑ j, A i j * ⟪highV (X i), fullV (Y j)⟫_ℝ)|
          + |(∑ i, ∑ j, A i j * ⟪lowV (X i), highV (Y j)⟫_ℝ)| :=
          abs_add_three _ _ _
      _ ≤ (64 * β) + (gtBound A * (1/4) * 1) + (gtBound A * 1 * (1/4)) :=
          add_le_add (add_le_add hS1 hS2) hS3
      _ = 64 * β + gtBound A / 2 := by ring

-- N14
theorem gtBound_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) {β : ℝ}
    (hsign : ∀ (ε : Fin m → ℝ) (δ : Fin n → ℝ),
      (∀ i, ε i = 1 ∨ ε i = -1) → (∀ j, δ j = 1 ∨ δ j = -1) →
      |∑ i : Fin m, ∑ j : Fin n, A i j * ε i * δ j| ≤ β) :
    gtBound A ≤ 128 * β := by
  have hstep : gtBound A ≤ 64 * β + gtBound A / 2 := by
    unfold gtBound
    apply csSup_le ⟨0, gtBound_mem_zero A⟩
    intro r hr
    obtain ⟨d, x, y, hx, hy, rfl⟩ := hr
    exact euclidean_self_improving_bound A hsign x y hx hy
  linarith

-- N15: the Wanted statement, K = 128
/--
There exists a universal `K>0` such that for every `m n`, real matrix `A`, real Hilbert space `H`,
and families `x : Fin m → H`, `y : Fin n → H` in the unit ball, some signs `ε i, δ j ∈ {±1}`
satisfy `|∑ A i j ⟪x i, y j⟫| ≤ K|∑ A i j ε i δ j|`. Source: A. Grothendieck, Resume de la theorie
metrique des produits tensoriels topologiques, Bol. Soc. Mat. Sao Paulo 8 (1953) 1-79, inequality;
Pisier, Grothendieck's theorem past and present, 2012; Lean states real finite-matrix scalarized
form with `Fin`-indexed unit vectors and `±1` signs, existential universal constant `K`.

Proves `Wanted` entry `grothendieck_inequality_real`.
-/
theorem grothendieck_inequality_real :
    ∃ K : ℝ, 0 < K ∧
      ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
        (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (x : Fin m → H) (y : Fin n → H),
        (∀ i, ‖x i‖ ≤ 1) → (∀ j, ‖y j‖ ≤ 1) →
        ∃ (ε : Fin m → ℝ) (δ : Fin n → ℝ),
          (∀ i, ε i = 1 ∨ ε i = -1) ∧
          (∀ j, δ j = 1 ∨ δ j = -1) ∧
          |∑ i : Fin m, ∑ j : Fin n, A i j * ⟪x i, y j⟫_ℝ| ≤
            K * |∑ i : Fin m, ∑ j : Fin n, A i j * ε i * δ j| := by
  refine ⟨128, by norm_num, fun m n A H _ _ _ x y hx hy => ?_⟩
  let σ : Bool → ℝ := fun b => if b then 1 else -1
  have hne : Nonempty ((Fin m → Bool) × (Fin n → Bool)) :=
    ⟨(fun _ => true, fun _ => true)⟩
  obtain ⟨⟨ps, qs⟩, hmax⟩ := @Finite.exists_max
    ((Fin m → Bool) × (Fin n → Bool)) ℝ inferInstance hne inferInstance
    (fun pq : (Fin m → Bool) × (Fin n → Bool) =>
      |∑ i, ∑ j, A i j * σ (pq.1 i) * σ (pq.2 j)|)
  refine ⟨fun i => σ (ps i), fun j => σ (qs j), ?_, ?_, ?_⟩
  · intro i
    cases h : ps i <;> simp [σ, h]
  · intro j
    cases h : qs j <;> simp [σ, h]
  · have hσε : ∀ (ε' : Fin m → ℝ), (∀ i, ε' i = 1 ∨ ε' i = -1) →
        ∀ i, σ (decide (ε' i = 1)) = ε' i := by
      intro ε' hε' i
      simp only [σ]
      split_ifs with hd
      · exact (of_decide_eq_true hd).symm
      · have hne : ¬ ε' i = 1 := of_decide_eq_false (Bool.eq_false_of_ne_true hd)
        have h2 : ε' i = -1 := by
          rcases hε' i with h1 | h1
          · exact absurd h1 hne
          · exact h1
        rw [h2]
    have hσδ : ∀ (δ' : Fin n → ℝ), (∀ j, δ' j = 1 ∨ δ' j = -1) →
        ∀ j, σ (decide (δ' j = 1)) = δ' j := by
      intro δ' hδ' j
      simp only [σ]
      split_ifs with hd
      · exact (of_decide_eq_true hd).symm
      · have hne : ¬ δ' j = 1 := of_decide_eq_false (Bool.eq_false_of_ne_true hd)
        have h2 : δ' j = -1 := by
          rcases hδ' j with h1 | h1
          · exact absurd h1 hne
          · exact h1
        rw [h2]
    have hsign : ∀ (ε' : Fin m → ℝ) (δ' : Fin n → ℝ),
        (∀ i, ε' i = 1 ∨ ε' i = -1) → (∀ j, δ' j = 1 ∨ δ' j = -1) →
        |∑ i : Fin m, ∑ j : Fin n, A i j * ε' i * δ' j|
          ≤ |∑ i, ∑ j, A i j * σ (ps i) * σ (qs j)| := by
      intro ε' δ' hε' hδ'
      have erew : (∑ i, ∑ j, A i j * ε' i * δ' j)
          = ∑ i, ∑ j, A i j * σ (decide (ε' i = 1)) * σ (decide (δ' j = 1)) := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        rw [hσε ε' hε' i, hσδ δ' hδ' j]
      rw [erew]
      exact hmax ⟨fun i => decide (ε' i = 1), fun j => decide (δ' j = 1)⟩
    have hN8 := abs_sum_inner_le_gtBound_mul (E := H) A (s := 1) (t := 1)
      (by norm_num) (by norm_num) x y hx hy
    have hN14 := gtBound_le A hsign
    calc |∑ i : Fin m, ∑ j : Fin n, A i j * ⟪x i, y j⟫_ℝ|
          ≤ gtBound A * 1 * 1 := hN8
        _ = gtBound A := by ring
        _ ≤ 128 * |∑ i, ∑ j, A i j * σ (ps i) * σ (qs j)| := hN14
        _ = 128 * |∑ i : Fin m, ∑ j : Fin n,
            A i j * (fun i => σ (ps i)) i * (fun j => σ (qs j)) j| := rfl

end FunctionalAnalysis.GrothendieckInequalityWanted
end
