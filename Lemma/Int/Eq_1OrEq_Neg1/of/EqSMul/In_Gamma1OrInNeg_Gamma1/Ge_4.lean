import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped MatrixGroups
open UpperHalfPlane
open CongruenceSubgroup


private lemma sq_trace_lt_four_or_eq_of_smul_eq (γ : SL(2, ℤ)) (τ : ℍ) (hτ : γ • τ = τ) :
  (γ 0 0 + γ 1 1) ^ 2 < 4 ∨ γ = 1 ∨ γ = -1 := by
  set g : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ γ with hg
  have hgij : ∀ i j, g i j = ((γ i j : ℤ) : ℝ) := fun i j => by
    simp [hg, Matrix.SpecialLinearGroup.mapGL, Matrix.SpecialLinearGroup.toGL]
  have hfix : g • τ = τ := hτ
  have hdet : g.val.det = 1 := by
    rw [Matrix.det_fin_two]
    simp only [hgij]
    have h := γ.2
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  have hdetpos : 0 < g.val.det := by simpa [hdet] using one_pos
  if hgc : g ∈ Subgroup.center (GL (Fin 2) ℝ) then
    right
    rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at hgc
    obtain ⟨r, hr⟩ := hgc
    have h00 : ((γ 0 0 : ℤ) : ℝ) = r := by rw [← hgij]; simp [← hr]
    have h11 : ((γ 1 1 : ℤ) : ℝ) = r := by rw [← hgij]; simp [← hr]
    have h01 : ((γ 0 1 : ℤ) : ℝ) = 0 := by rw [← hgij]; simp [← hr]
    have h10 : ((γ 1 0 : ℤ) : ℝ) = 0 := by rw [← hgij]; simp [← hr]
    have e01 : γ 0 1 = 0 := by exact_mod_cast h01
    have e10 : γ 1 0 = 0 := by exact_mod_cast h10
    have e0011 : γ 0 0 = γ 1 1 := by exact_mod_cast h00.trans h11.symm
    have hd := γ.2
    rw [Matrix.det_fin_two, e01, e10, ← e0011, mul_zero, sub_zero] at hd
    have hsq : γ 0 0 = 1 ∨ γ 0 0 = -1 := by
      obtain h | h := Int.eq_one_or_neg_one_of_mul_eq_one hd
      · exact Or.inl h
      · exact Or.inr h
    obtain h1 | h1 := hsq
    ·
      left
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h1, e01, e10, ← e0011]
    ·
      right
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h1, e01, e10, ← e0011]
  else
    left
    have hell := UpperHalfPlane.isElliptic_of_exists_smul_eq_self hdetpos hgc ⟨τ, hfix⟩
    have h' : g.val.discr < 0 := hell
    rw [Matrix.discr_fin_two, Matrix.trace_fin_two, hdet] at h'
    have h'' : (((γ 0 0 + γ 1 1 : ℤ) : ℝ)) ^ 2 < 4 := by
      push_cast
      rw [← hgij 0 0, ← hgij 1 1]
      linarith
    exact_mod_cast h''
private lemma eq_one_or_eq_neg_one_of_mem_Gamma1_of_smul_eq (M : ℕ) (hM : 4 ≤ M) (γ : SL(2, ℤ))
  (hγ : γ ∈ Gamma1 M ∨ -γ ∈ Gamma1 M) (τ : ℍ) (hτ : γ • τ = τ) : γ = 1 ∨ γ = -1 := by
  obtain hlt | h | h := sq_trace_lt_four_or_eq_of_smul_eq γ τ hτ
  ·
    exfalso
    set t : ℤ := γ 0 0 + γ 1 1 with ht
    have ht1 : -1 ≤ t ∧ t ≤ 1 := by constructor <;> nlinarith
    have hdvd : (M : ℤ) ∣ t - 2 ∨ (M : ℤ) ∣ t + 2 := by
      obtain h | h := hγ
      ·
        left
        rw [Gamma1_mem] at h
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ht]
        push_cast
        rw [h.1, h.2.1]
        norm_num
      ·
        right
        rw [Gamma1_mem] at h
        have h0 : (((-γ) 0 0 : ℤ) : ZMod M) = 1 := h.1
        have h1 : (((-γ) 1 1 : ℤ) : ZMod M) = 1 := h.2.1
        rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, neg_eq_iff_eq_neg] at h0 h1
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ht]
        push_cast
        rw [h0, h1]
        norm_num
    have hM' : (4 : ℤ) ≤ M := by exact_mod_cast hM
    obtain hd | hd := hdvd
    ·
      have hne : t - 2 ≠ 0 := by omega
      have hle := Int.le_of_dvd (by omega : 0 < -(t - 2)) ((dvd_neg).mpr hd)
      omega
    ·
      have hle := Int.le_of_dvd (by omega : 0 < t + 2) hd
      omega
  · exact Or.inl h
  · exact Or.inr h
/--
[CongruenceSubgroup_eq_one_or_eq_neg_one_of_mem_Gamma1_of_smul_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CongruenceSubgroup_eq_one_or_eq_neg_one_of_mem_Gamma1_of_smul_eq.lean)
-/
@[path]
private lemma main
  {M : ℕ}
  {γ : SL(2, ℤ)}
  {τ : UpperHalfPlane}
-- given
  (hM : 4 ≤ M)
  (hγ : γ ∈ CongruenceSubgroup.Gamma1 M ∨ -γ ∈ CongruenceSubgroup.Gamma1 M)
  (hτ : γ • τ = τ) :
-- imply
  γ = 1 ∨ γ = -1 :=
-- proof
  eq_one_or_eq_neg_one_of_mem_Gamma1_of_smul_eq M hM γ hγ τ hτ


-- created on 2026-10-23
