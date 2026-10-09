import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import sympy.Basic

open scoped Matrix

@[path]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
  {A : Matrix S S ℝ}
-- given
  (h₀ : ∀ i j, 0 ≤ A i j)
  (h₁ : ∀ i j, ∃ n > 0, 0 < (A ^ n) i j) :
-- imply
  ∃ l : ℝ, 0 < l ∧ ∃ q : S → ℝ, (∀ k, 0 < q k) ∧ A *ᵥ q = l • q := by
-- proof
  choose n hn hpos using h₁
  let N : ℕ := Finset.univ.sup (fun ij : S × S => n ij.1 ij.2) + 1
  have hN : 0 < N := Nat.succ_pos _
  let B : Matrix S S ℝ := ∑ k ∈ Finset.range N, A ^ k
  have hAn : ∀ k i j, 0 ≤ (A ^ k) i j := fun k => Matrix.pow_apply_nonneg h₀ k
  have hB : ∀ i j, 0 < B i j := by
    intro i j
    have hlt : n i j < N := by
      apply Nat.lt_succ_of_le (Finset.le_sup (f := fun ij : S × S => n ij.1 ij.2) (Finset.mem_univ (i, j)))
    simp only [B, Matrix.sum_apply]
    apply lt_of_lt_of_le (hpos i j)
    apply Finset.single_le_sum (f := fun k => (A ^ k) i j) (fun k _ => hAn k i j) (Finset.mem_range.2 hlt)
  have hBA : A * B = B * A := by
    simp only [B, Finset.mul_sum, Finset.sum_mul, ← pow_succ, ← pow_succ']
  have hBpos : ∀ w : S → ℝ, (∀ k, 0 ≤ w k) → (∃ k, 0 < w k) → ∀ i, 0 < (B *ᵥ w) i := by
    intro w hw ⟨k, hk⟩ i
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_pos' (fun j _ => mul_nonneg (hB i j).le (hw j)) ⟨k, Finset.mem_univ k, mul_pos (hB i k) hk⟩
  have hbound : ∀ y ∈ stdSimplex ℝ S, ∀ ρ : ℝ, (∀ i, ρ * y i ≤ (A *ᵥ y) i) → ρ ≤ ∑ i, ∑ j, A i j := by
    intro y hy ρ h
    calc
      _ = ∑ i, ρ * y i := by rw [← Finset.mul_sum, hy.2, mul_one]
      _ ≤ ∑ i, (A *ᵥ y) i := Finset.sum_le_sum fun i _ => h i
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        simp only [Matrix.mulVec, dotProduct]
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_of_le_one_right (h₀ i j) (mem_Icc_of_mem_stdSimplex hy j).2
  let E : Set ((S → ℝ) × ℝ) := {p | p.1 ∈ stdSimplex ℝ S ∧ 0 ≤ p.2 ∧ ∀ i, p.2 * p.1 i ≤ (A *ᵥ p.1) i}
  have hEc : IsClosed E := by
    have : E = (Prod.fst ⁻¹' stdSimplex ℝ S) ∩ ((Prod.snd ⁻¹' Set.Ici 0) ∩ ⋂ i, {p : (S → ℝ) × ℝ | p.2 * p.1 i ≤ (A *ᵥ p.1) i}) := by
      ext p
      simp [E]
    rw [this]
    refine (isClosed_stdSimplex ℝ S).preimage continuous_fst |>.inter (isClosed_Ici.preimage continuous_snd |>.inter (isClosed_iInter fun i => ?_))
    apply isClosed_le
    · fun_prop
    · simp only [Matrix.mulVec, dotProduct]
      fun_prop
  have hE : IsCompact E := by
    apply IsCompact.of_isClosed_subset ((isCompact_stdSimplex ℝ S).prod (isCompact_Icc (a := (0 : ℝ)) (b := ∑ i, ∑ j, A i j))) hEc
    intro p hp
    exact ⟨hp.1, hp.2.1, hbound p.1 hp.1 p.2 hp.2.2⟩
  have hne : E.Nonempty := by
    refine ⟨(Pi.single (Classical.arbitrary S) 1, 0), single_mem_stdSimplex ℝ _, le_rfl, fun i => ?_⟩
    simp only [zero_mul]
    apply Finset.sum_nonneg fun j _ => mul_nonneg (h₀ i j) ?_
    simp [Pi.single_apply]
    split_ifs <;> norm_num
  obtain ⟨⟨y, ρ⟩, hp₀, hmax⟩ := hE.exists_isMaxOn hne continuous_snd.continuousOn
  obtain ⟨hy, hρ, hyρ⟩ := hp₀
  simp only at hy hρ hyρ
  have hy0 : ∀ i, 0 ≤ y i := hy.1
  have hyk : ∃ k, 0 < y k := by
    by_contra h
    push Not at h
    have : ∑ i, y i ≤ 0 := Finset.sum_nonpos fun i _ => h i
    linarith [hy.2]
  let w : S → ℝ := A *ᵥ y - ρ • y
  have hw0 : ∀ i, 0 ≤ w i := by
    intro i
    simp only [w, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith [hyρ i]
  have hweq : w = 0 := by
    by_contra hne
    have hwk : ∃ k, 0 < w k := by
      by_contra h
      push Not at h
      apply hne
      funext k
      exact le_antisymm (h k) (hw0 k)
    let z : S → ℝ := B *ᵥ y
    have hz : ∀ i, 0 < z i := hBpos y hy0 hyk
    have hAz : A *ᵥ z - ρ • z = B *ᵥ w := by
      simp only [z, w, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hBA]
    have hBw : ∀ i, 0 < (B *ᵥ w) i := hBpos w hw0 hwk
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ (fun i => (B *ᵥ w) i / z i) Finset.univ_nonempty
    have hε : 0 < (B *ᵥ w) i₀ / z i₀ := div_pos (hBw i₀) (hz i₀)
    have hεz : ∀ i, (B *ᵥ w) i₀ / z i₀ * z i ≤ (B *ᵥ w) i := by
      intro i
      have := hi₀ i (Finset.mem_univ i)
      exact (le_div_iff₀ (hz i)).1 this
    have hs : 0 < ∑ i, z i := Finset.sum_pos (fun i _ => hz i) Finset.univ_nonempty
    have hmem : ((∑ i, z i)⁻¹ • z, ρ + (B *ᵥ w) i₀ / z i₀) ∈ E := by
      refine ⟨⟨fun i => ?_, ?_⟩, by linarith, fun i => ?_⟩
      · exact mul_nonneg (inv_nonneg.2 hs.le) (hz i).le
      · simp only [Pi.smul_apply, smul_eq_mul]
        rw [← Finset.mul_sum, inv_mul_cancel₀ hs.ne']
      · simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
        have h1 := congrFun hAz i
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1
        have h2 := hεz i
        calc
          _ = (∑ i, z i)⁻¹ * ((ρ + (B *ᵥ w) i₀ / z i₀) * z i) := by ring
          _ ≤ _ := by
            apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 hs.le)
            nlinarith
    have := isMaxOn_iff.1 hmax _ hmem
    simp only at this
    linarith
  have hyeq : A *ᵥ y = ρ • y := sub_eq_zero.1 hweq
  have hpow : ∀ k, (A ^ k) *ᵥ y = ρ ^ k • y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hyeq, smul_smul, pow_succ]
  have hBy : B *ᵥ y = (∑ k ∈ Finset.range N, ρ ^ k) • y := by
    simp only [B, Matrix.sum_mulVec, hpow, Finset.sum_smul]
  have hc : 0 < ∑ k ∈ Finset.range N, ρ ^ k := by
    apply lt_of_lt_of_le one_pos
    simpa using Finset.single_le_sum (f := fun k => ρ ^ k) (fun k _ => pow_nonneg hρ k) (Finset.mem_range.2 hN)
  have hypos : ∀ i, 0 < y i := by
    intro i
    have := hBpos y hy0 hyk i
    rw [hBy] at this
    simpa [hc] using this
  refine ⟨ρ, ?_, y, hypos, hyeq⟩
  apply lt_of_le_of_ne hρ
  intro h0
  subst h0
  have hA0 : ∀ i j, A i j = 0 := by
    intro i j
    have := congrFun hyeq i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, zero_smul] at this
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (h₀ i j) (hy0 j))).1 this j (Finset.mem_univ j)
    simpa [(hypos j).ne'] using h2
  obtain ⟨m, hm⟩ : ∃ m, n (Classical.arbitrary S) (Classical.arbitrary S) = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos (hn _ _)).symm⟩
  have := hpos (Classical.arbitrary S) (Classical.arbitrary S)
  rw [hm, pow_succ', Matrix.mul_apply] at this
  simp [hA0] at this


-- created on 2026-09-29