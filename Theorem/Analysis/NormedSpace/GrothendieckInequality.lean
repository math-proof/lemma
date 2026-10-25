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
import Def.Analysis.NormedSpace.GrothendieckInequality
open scoped InnerProductSpace


section

namespace FunctionalAnalysis.GrothendieckInequalityWanted

-- N5
theorem truncAt_facts {M t : ℝ} (hM : 0 < M) :
    |truncAt M t| ≤ M ∧ (truncAt M t)^2 ≤ t^2 ∧ (t - truncAt M t)^2 * M^2 ≤ t^4 := by
  unfold truncAt
  by_cases h : |t| ≤ M
  · rw [ite_eq_left h]
    refine ⟨h, le_refl _, ?_⟩
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_mul]
    positivity
  · rw [ite_eq_right h]
    have hlt : M < |t| := lt_of_not_ge h
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_zero]; exact le_of_lt hM
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact sq_nonneg t
    · simp only [sub_zero]
      have hM2 : M^2 ≤ t^2 := by
        have h1 : M ≤ |t| := le_of_lt hlt
        calc M^2 ≤ |t|^2 := by
              apply sq_le_sq.mpr
              rw [abs_of_pos hM, abs_abs]
              exact h1
          _ = t^2 := sq_abs t
      have ht2 : 0 ≤ t^2 := sq_nonneg t
      calc t^2 * M^2 ≤ t^2 * t^2 := by
            apply mul_le_mul_of_nonneg_left hM2 ht2
        _ = t^4 := by ring

-- N2 helpers
theorem flipAt_involutive {d : ℕ} (k : Fin d) : Function.Involutive (flipAt k) := by
  intro ω
  simp [flipAt]

theorem radSign_flip_self {d : ℕ} (k : Fin d) (ω : Fin d → Bool) :
    radSign k (flipAt k ω) = -radSign k ω := by
  simp [radSign, flipAt, Function.update_self]
  by_cases h : ω k <;> simp [h]

theorem radSign_flip_ne {d : ℕ} {k l : Fin d} (hkl : l ≠ k) (ω : Fin d → Bool) :
    radSign l (flipAt k ω) = radSign l ω := by
  simp [radSign, flipAt, Function.update_of_ne hkl]

theorem radSign_sq {d : ℕ} (k : Fin d) (ω : Fin d → Bool) :
    radSign k ω * radSign k ω = 1 := by
  simp [radSign]
  by_cases h : ω k <;> simp [h]

-- N2
theorem radSign_flip_sum_eq_zero {d : ℕ} (k : Fin d)
    (f : (Fin d → Bool) → ℝ) (hf : ∀ ω, f (flipAt k ω) = f ω) :
    ∑ ω, f ω * radSign k ω = 0 := by
  have hperm : ∀ ω, f (flipAt k ω) * radSign k (flipAt k ω) = -(f ω * radSign k ω) := by
    intro ω
    rw [hf ω, radSign_flip_self k ω]
    ring
  have hS : ∑ ω, f (flipAt k ω) * radSign k (flipAt k ω) = ∑ ω, f ω * radSign k ω := by
    have h := Equiv.sum_comp ((flipAt_involutive k).toPerm) (fun ω => f ω * radSign k ω)
    simpa [Function.Involutive.toPerm] using h
  have hneg : ∑ ω, f (flipAt k ω) * radSign k (flipAt k ω) = -(∑ ω, f ω * radSign k ω) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun ω _ => hperm ω)
  linarith

-- N1 (part2)
theorem abs_bilinear_le_sq_mul_of_sign_bound
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) {M β : ℝ} (hM : 0 ≤ M)
    (hsign : ∀ (ε : Fin m → ℝ) (δ : Fin n → ℝ),
      (∀ i, ε i = 1 ∨ ε i = -1) → (∀ j, δ j = 1 ∨ δ j = -1) →
      |∑ i : Fin m, ∑ j : Fin n, A i j * ε i * δ j| ≤ β)
    (a : Fin m → ℝ) (b : Fin n → ℝ)
    (ha : ∀ i, |a i| ≤ M) (hb : ∀ j, |b j| ≤ M) :
    |∑ i : Fin m, ∑ j : Fin n, A i j * a i * b j| ≤ M^2 * β := by
  set c : Fin m → ℝ := fun i => ∑ j, A i j * b j with hc
  set ε : Fin m → ℝ := fun i => if 0 ≤ c i then 1 else -1 with hε
  have hεsign : ∀ i, ε i = 1 ∨ ε i = -1 := by
    intro i
    simp only [hε]
    by_cases h : 0 ≤ c i <;> simp [h]
  have hεc : ∀ i, ε i * c i = |c i| := by
    intro i
    simp only [hε]
    by_cases h : 0 ≤ c i
    · rw [ite_eq_left h, one_mul, abs_of_nonneg h]
    · rw [ite_eq_right h, neg_one_mul, abs_of_neg (lt_of_not_ge h)]
  have hS : (∑ i : Fin m, ∑ j : Fin n, A i j * a i * b j) = ∑ i, a i * c i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  set d : Fin n → ℝ := fun j => ∑ i, A i j * ε i with hd
  set δ : Fin n → ℝ := fun j => if 0 ≤ d j then 1 else -1 with hδ
  have hδsign : ∀ j, δ j = 1 ∨ δ j = -1 := by
    intro j
    simp only [hδ]
    by_cases h : 0 ≤ d j <;> simp [h]
  have hδd : ∀ j, δ j * d j = |d j| := by
    intro j
    simp only [hδ]
    by_cases h : 0 ≤ d j
    · rw [ite_eq_left h, one_mul, abs_of_nonneg h]
    · rw [ite_eq_right h, neg_one_mul, abs_of_neg (lt_of_not_ge h)]
  have hT : (∑ i, ε i * c i) = ∑ j, d j * b j := by
    have e1 : (∑ i, ε i * c i) = ∑ i, ∑ j, ε i * (A i j * b j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hc, Finset.mul_sum]
    have e2 : (∑ i, ∑ j, ε i * (A i j * b j)) = ∑ j, ∑ i, ε i * (A i j * b j) :=
      Finset.sum_comm
    have e3 : (∑ j, ∑ i, ε i * (A i j * b j)) = ∑ j, d j * b j := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [hd]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [e1, e2, e3]
  have hU : (∑ j, δ j * d j) = ∑ i : Fin m, ∑ j : Fin n, A i j * ε i * δ j := by
    simp only [hd]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hUbound : |∑ j, δ j * d j| ≤ β := by
    rw [hU]
    exact hsign ε δ hεsign hδsign
  have hST : |∑ i, a i * c i| ≤ M * |∑ i, ε i * c i| := by
    have h1 : |∑ i, a i * c i| ≤ ∑ i, M * |c i| := by
      calc |∑ i, a i * c i| ≤ ∑ i, |a i * c i| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ i, |a i| * |c i| := by
              apply Finset.sum_congr rfl; intro i _; rw [abs_mul]
        _ ≤ ∑ i, M * |c i| := by
              apply Finset.sum_le_sum
              intro i _
              apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
              exact ha i
    have heq : (∑ i, ε i * c i) = ∑ i, |c i| :=
      Finset.sum_congr rfl (fun i _ => hεc i)
    have h2 : (∑ i, M * |c i|) = M * |∑ i, ε i * c i| := by
      rw [heq, abs_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _)),
        Finset.mul_sum]
    rwa [h2] at h1
  have hTU : |∑ j, d j * b j| ≤ M * |∑ j, δ j * d j| := by
    have h1 : |∑ j, d j * b j| ≤ ∑ j, M * |d j| := by
      calc |∑ j, d j * b j| ≤ ∑ j, |d j * b j| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j, |d j| * |b j| := by
              apply Finset.sum_congr rfl; intro j _; rw [abs_mul]
        _ ≤ ∑ j, |d j| * M := by
              apply Finset.sum_le_sum
              intro j _
              apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
              exact hb j
        _ = ∑ j, M * |d j| := by
              apply Finset.sum_congr rfl; intro j _; ring
    have heq : (∑ j, δ j * d j) = ∑ j, |d j| :=
      Finset.sum_congr rfl (fun j _ => hδd j)
    have h2 : (∑ j, M * |d j|) = M * |∑ j, δ j * d j| := by
      rw [heq, abs_of_nonneg (Finset.sum_nonneg (fun j _ => abs_nonneg _)),
        Finset.mul_sum]
    rwa [h2] at h1
  rw [hS]
  calc |∑ i, a i * c i| ≤ M * |∑ i, ε i * c i| := hST
    _ = M * |∑ j, d j * b j| := by rw [hT]
    _ ≤ M * (M * |∑ j, δ j * d j|) := by
          apply mul_le_mul_of_nonneg_left hTU hM
    _ ≤ M * (M * β) := by
          apply mul_le_mul_of_nonneg_left _ hM
          apply mul_le_mul_of_nonneg_left hUbound hM
    _ = M^2 * β := by ring

-- N3 (part3)
theorem card_cube (d : ℕ) : (Fintype.card (Fin d → Bool) : ℝ) = (2:ℝ)^d := by
  simp [Nat.cast_pow]

-- N3: orthonormality of Rademacher functions
theorem radSign_second_moment {d : ℕ} (s : Finset (Fin d)) (a b : Fin d → ℝ) :
    ∑ ω : Fin d → Bool, (∑ k ∈ s, radSign k ω * a k) * (∑ l ∈ s, radSign l ω * b l)
      = (2:ℝ)^d * ∑ k ∈ s, a k * b k := by
  have pair : ∀ k ∈ s, ∀ l ∈ s,
      (∑ ω : Fin d → Bool, (radSign k ω * a k) * (radSign l ω * b l))
        = (if l = k then (2:ℝ)^d else 0) * (a k * b l) := by
    intro k _ l _
    have e1 : ∀ ω : Fin d → Bool, (radSign k ω * a k) * (radSign l ω * b l)
        = (a k * b l) * (radSign k ω * radSign l ω) := fun ω => by ring
    rw [Finset.sum_congr rfl (fun ω _ => e1 ω), ← Finset.mul_sum]
    split_ifs with hkl
    · subst hkl
      have e2 : (∑ ω : Fin d → Bool, radSign l ω * radSign l ω)
          = ∑ _ω : Fin d → Bool, (1:ℝ) :=
        Finset.sum_congr rfl (fun ω _ => radSign_sq l ω)
      rw [e2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_cube]
      ring
    · have hne : k ≠ l := fun h => hkl h.symm
      have e2 : (∑ ω : Fin d → Bool, radSign k ω * radSign l ω) = 0 := by
        have h := radSign_flip_sum_eq_zero (d := d) l (fun ω => radSign k ω)
          (fun ω => radSign_flip_ne hne ω)
        exact h
      rw [e2, mul_zero, zero_mul]
  have step : ∀ ω : Fin d → Bool,
      (∑ k ∈ s, radSign k ω * a k) * (∑ l ∈ s, radSign l ω * b l)
        = ∑ k ∈ s, ∑ l ∈ s, (radSign k ω * a k) * (radSign l ω * b l) := by
    intro ω
    exact Finset.sum_mul_sum s s _ _
  calc ∑ ω : Fin d → Bool, (∑ k ∈ s, radSign k ω * a k) * (∑ l ∈ s, radSign l ω * b l)
        = ∑ k ∈ s, ∑ l ∈ s, ∑ ω : Fin d → Bool,
            (radSign k ω * a k) * (radSign l ω * b l) := by
          rw [Finset.sum_congr rfl (fun ω _ => step ω), Finset.sum_comm]
          exact Finset.sum_congr rfl (fun k _ => Finset.sum_comm)
      _ = ∑ k ∈ s, ∑ l ∈ s, (if l = k then (2:ℝ)^d else 0) * (a k * b l) := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro l hl
          exact pair k hk l hl
      _ = ∑ k ∈ s, (2:ℝ)^d * (a k * b k) := by
          apply Finset.sum_congr rfl
          intro k hk
          have e : ∀ l ∈ s, (if l = k then (2:ℝ)^d else 0) * (a k * b l)
              = (if l = k then (2:ℝ)^d * (a k * b l) else 0) := by
            intro l _
            split_ifs with h <;> ring
          rw [Finset.sum_congr rfl e, Finset.sum_ite_eq']
          simp [hk]
      _ = (2:ℝ)^d * ∑ k ∈ s, a k * b k := by
          rw [Finset.mul_sum]

-- N4 (part4)
-- pointwise fourth-power expansion under r*r = 1
theorem fourth_expand {u rr c : ℝ} (hrr : rr * rr = 1) :
    (u + rr * c)^4
      = u^4 + 4 * c * (u^3 * rr) + 6 * c^2 * u^2 + 4 * c^3 * (u * rr) + c^4 := by
  have hrr2 : rr^2 = 1 := by
    have : rr^2 = rr * rr := by ring
    rw [this, hrr]
  have hrr3 : rr^3 = rr := by
    calc rr^3 = rr^2 * rr := by ring
      _ = 1 * rr := by rw [hrr2]
      _ = rr := one_mul rr
  have hrr4 : rr^4 = 1 := by
    calc rr^4 = rr^2 * rr^2 := by ring
      _ = 1 * 1 := by rw [hrr2]
      _ = 1 := one_mul 1
  have binom : (u + rr * c)^4
      = u^4 + 4*u^3*(rr*c) + 6*u^2*(rr*c)^2 + 4*u*(rr*c)^3 + (rr*c)^4 := by ring
  have sq : (rr*c)^2 = c^2 := by
    calc (rr*c)^2 = rr^2*c^2 := by ring
      _ = 1 * c^2 := by rw [hrr2]
      _ = c^2 := one_mul _
  have cb : (rr*c)^3 = c^3*rr := by
    calc (rr*c)^3 = rr^3*c^3 := by ring
      _ = rr * c^3 := by rw [hrr3]
      _ = c^3*rr := mul_comm _ _
  have q4 : (rr*c)^4 = c^4 := by
    calc (rr*c)^4 = rr^4*c^4 := by ring
      _ = 1 * c^4 := by rw [hrr4]
      _ = c^4 := one_mul _
  rw [binom, sq, cb, q4]
  ring

-- N4: fourth-moment Khintchine bound with constant 3
theorem radSign_fourth_moment_le {d : ℕ} (s : Finset (Fin d)) (a : Fin d → ℝ) :
    ∑ ω : Fin d → Bool, (∑ k ∈ s, radSign k ω * a k)^4
      ≤ 3 * (2:ℝ)^d * (∑ k ∈ s, a k ^ 2)^2 := by
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro j t hjt ih
    -- abbreviate the old sum and old squares
    set U : (Fin d → Bool) → ℝ := fun ω => ∑ k ∈ t, radSign k ω * a k with hU
    set S : ℝ := ∑ k ∈ t, a k ^ 2 with hS
    have hUinv : ∀ ω, U (flipAt j ω) = U ω := by
      intro ω
      simp only [hU]
      apply Finset.sum_congr rfl
      intro k hk
      have hkj : k ≠ j := fun h => hjt (h ▸ hk)
      rw [radSign_flip_ne hkj]
    have odd3 : (∑ ω : Fin d → Bool, U ω ^ 3 * radSign j ω) = 0 := by
      have h := radSign_flip_sum_eq_zero (d := d) j (fun ω => U ω ^ 3)
        (fun ω => by rw [hUinv ω])
      simpa [pow_three, mul_assoc] using h
    have odd1 : (∑ ω : Fin d → Bool, U ω * radSign j ω) = 0 :=
      radSign_flip_sum_eq_zero (d := d) j U hUinv
    have sqU : (∑ ω : Fin d → Bool, U ω ^ 2) = (2:ℝ)^d * S := by
      have h := radSign_second_moment (d := d) t a a
      have e1 : (∑ ω : Fin d → Bool, U ω ^ 2)
          = ∑ ω : Fin d → Bool, (∑ k ∈ t, radSign k ω * a k)
              * (∑ k ∈ t, radSign k ω * a k) := by
        simp only [hU]
        apply Finset.sum_congr rfl
        intro ω _
        rw [sq]
      have e2 : (∑ k ∈ t, a k * a k) = S := by
        simp only [hS]
        apply Finset.sum_congr rfl
        intro k _
        rw [sq]
      rw [e1, ← e2]
      exact h
    have const4 : (∑ _ω : Fin d → Bool, (a j)^4) = (2:ℝ)^d * (a j)^4 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_cube]
    -- expand the new sum
    have expand : ∀ ω : Fin d → Bool,
        (∑ k ∈ insert j t, radSign k ω * a k)^4
        = U ω^4 + 4 * a j * (U ω^3 * radSign j ω)
          + 6 * (a j)^2 * U ω^2 + 4 * (a j)^3 * (U ω * radSign j ω) + (a j)^4 := by
      intro ω
      have eU : (∑ k ∈ insert j t, radSign k ω * a k)
          = U ω + radSign j ω * a j := by
        simp only [hU]
        rw [Finset.sum_insert hjt]
        ring
      rw [eU]
      exact fourth_expand (radSign_sq j ω)
    have h2d : (0:ℝ) ≤ (2:ℝ)^d := by positivity
    have hS2 : (0:ℝ) ≤ S^2 := sq_nonneg S
    have haj4 : (0:ℝ) ≤ ((2:ℝ)^d) * (a j)^4 := by positivity
    calc ∑ ω : Fin d → Bool, (∑ k ∈ insert j t, radSign k ω * a k)^4
          = ∑ ω : Fin d → Bool, (U ω^4 + 4 * a j * (U ω^3 * radSign j ω)
              + 6 * (a j)^2 * U ω^2 + 4 * (a j)^3 * (U ω * radSign j ω) + (a j)^4) := by
            apply Finset.sum_congr rfl
            intro ω _
            exact expand ω
        _ = (∑ ω : Fin d → Bool, U ω^4)
              + 4 * a j * (∑ ω : Fin d → Bool, U ω^3 * radSign j ω)
              + 6 * (a j)^2 * (∑ ω : Fin d → Bool, U ω ^ 2)
              + 4 * (a j)^3 * (∑ ω : Fin d → Bool, U ω * radSign j ω)
              + (∑ _ω : Fin d → Bool, (a j)^4) := by
            simp only [Finset.sum_add_distrib, Finset.mul_sum]
        _ = (∑ ω : Fin d → Bool, U ω^4)
              + 6 * (a j)^2 * ((2:ℝ)^d * S) + ((2:ℝ)^d * (a j)^4) := by
            rw [odd3, odd1, sqU, const4]
            ring
        _ ≤ 3 * (2:ℝ)^d * S^2 + 6 * (a j)^2 * ((2:ℝ)^d * S)
              + 3 * ((2:ℝ)^d * (a j)^4) := by
            have h := ih
            simp only [hS] at h
            have hle : (∑ ω : Fin d → Bool, U ω ^ 4) ≤ 3 * (2:ℝ)^d * S^2 := by
              simpa [hU] using h
            have h34 : (2:ℝ)^d * (a j)^4 ≤ 3 * ((2:ℝ)^d * (a j)^4) := by
              linarith [haj4]
            linarith
        _ = 3 * (2:ℝ)^d * (S + (a j)^2)^2 := by ring
        _ = 3 * (2:ℝ)^d * (∑ k ∈ insert j t, a k ^ 2)^2 := by
            rw [Finset.sum_insert hjt, hS]
            ring

-- N6-N8 (part5)
-- N6: finite families embed isometrically into some EuclideanSpace
theorem exists_euclidean_isometric_copy {m n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : Fin m → E) (y : Fin n → E) :
    ∃ d : ℕ, ∃ X : Fin m → EuclideanSpace ℝ (Fin d),
      ∃ Y : Fin n → EuclideanSpace ℝ (Fin d),
      (∀ i, ‖X i‖ = ‖x i‖) ∧ (∀ j, ‖Y j‖ = ‖y j‖) ∧
      (∀ i j, ⟪X i, Y j⟫_ℝ = ⟪x i, y j⟫_ℝ) := by
  have hfin : (Set.range x ∪ Set.range y).Finite :=
    (Set.finite_range x).union (Set.finite_range y)
  have : FiniteDimensional ℝ (Submodule.span ℝ (Set.range x ∪ Set.range y)) :=
    FiniteDimensional.span_of_finite ℝ hfin
  let b := stdOrthonormalBasis ℝ (Submodule.span ℝ (Set.range x ∪ Set.range y))
  refine ⟨Module.finrank ℝ (Submodule.span ℝ (Set.range x ∪ Set.range y)),
    fun i => b.repr ⟨x i, Submodule.subset_span (Set.mem_union_left _ (Set.mem_range_self i))⟩,
    fun j => b.repr ⟨y j, Submodule.subset_span (Set.mem_union_right _ (Set.mem_range_self j))⟩,
    ?_, ?_, ?_⟩
  · intro i
    rw [b.repr.norm_map]
    exact (Submodule.norm_coe _).symm
  · intro j
    rw [b.repr.norm_map]
    exact (Submodule.norm_coe _).symm
  · intro i j
    rw [b.repr.inner_map_map]
    exact Submodule.coe_inner _ _ _

end FunctionalAnalysis.GrothendieckInequalityWanted
end
