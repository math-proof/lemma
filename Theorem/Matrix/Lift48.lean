module

public import Def.LanglandsTunnell_ExplicitLift
public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Instance.LanglandsTunnell_Lift48
public import Abbrev.LanglandsTunnell_Lift48

public section

set_option autoImplicit false

namespace Matrix.Lift48

open FLT.ExplicitLift Matrix


public theorem K48_eq_map_evalWord : K48 = W48.map evalWord := by decide


public theorem length_K48 : K48.length = 48 := by decide


public theorem nodup_K48 : K48.Nodup := by decide


public theorem one_mem_K48 : (1 : Mat) ∈ K48 := by decide


public theorem Slift_mem_K48 : Slift ∈ K48 := by decide


public theorem Tlift_mem_K48 : Tlift ∈ K48 := by decide


public theorem Slift_mul_mem_K48 : ∀ k ∈ K48, Slift * k ∈ K48 := by decide


public theorem Tlift_mul_mem_K48 : ∀ k ∈ K48, Tlift * k ∈ K48 := by decide


public theorem evalWord_mem_closure (w : List (Fin 2)) :
    evalWord w ∈ Submonoid.closure ({Slift, Tlift} : Set Mat) := by
  induction w with
  | nil => exact Submonoid.one_mem _
  | cons a w ih =>
    match a with
    | 0 => exact Submonoid.mul_mem _ (Submonoid.subset_closure (by simp)) ih
    | 1 => exact Submonoid.mul_mem _ (Submonoid.subset_closure (by simp)) ih


public theorem mem_closure_iff_mem_K48 (k : Mat) :
    k ∈ Submonoid.closure ({Slift, Tlift} : Set Mat) ↔ k ∈ K48 := by
  constructor
  · intro hk
    induction hk using Submonoid.closure_induction_left with
    | one => exact one_mem_K48
    | mul_left x hx y hy ih =>
      rcases hx with rfl | rfl
      · exact Slift_mul_mem_K48 y ih
      · exact Tlift_mul_mem_K48 y ih
  · intro hk
    have h := K48_eq_map_evalWord ▸ hk
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 h
    exact evalWord_mem_closure w


public theorem negTcube_mul_mem_K48 : ∀ k ∈ K48, -(Tlift * Tlift * Tlift) * k ∈ K48 := by decide


public theorem pw_eq_pow (A : Mat) (n : ℕ) : pw A n = A ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pw, ih, pow_succ']


public theorem det2_eq_det (A : Mat) : det2 A = A.det := (Matrix.det_fin_two A).symm


public theorem tr2_eq_trace (A : Mat) : tr2 A = A.trace := (Matrix.trace_fin_two A).symm


public theorem K48_projOrder_cases : ∀ k ∈ K48, IsPM1 k ∨ IsProjOrder 2 k ∨ IsProjOrder 3 k ∨ IsProjOrder 4 k := by
  decide


public theorem K48_det_cases : ∀ k ∈ K48, det2 k = 1 ∨ det2 k = -1 := by decide


public theorem K48_row_central : ∀ k ∈ K48, IsPM1 k → det2 k = 1 ∧ (tr2 k = 2 ∨ tr2 k = -2) := by decide


public theorem K48_row_two_odd : ∀ k ∈ K48, IsProjOrder 2 k → det2 k = -1 → tr2 k = 0 := by decide


public theorem K48_row_two_even : ∀ k ∈ K48, IsProjOrder 2 k → det2 k = 1 → tr2 k = 0 ∧ pw k 4 = 1 := by decide


public theorem K48_row_three : ∀ k ∈ K48, IsProjOrder 3 k → det2 k = 1 ∧ tr2 k * tr2 k = det2 k := by decide


public theorem K48_row_four : ∀ k ∈ K48, IsProjOrder 4 k → det2 k = -1 ∧ (tr2 k = ⟨0, 1⟩ ∨ tr2 k = ⟨0, -1⟩) := by
  decide


public theorem K48_row_four_classes : ∀ k ∈ K48, IsProjOrder 4 k →
    (tr2 k = ⟨0, 1⟩ → ∃ g ∈ K48, g * k = Tlift * g) ∧ (tr2 k = ⟨0, -1⟩ → ∃ g ∈ K48, g * k = -Tlift * g) := by
  decide


public theorem K48_order8_pair :
    (∀ g ∈ K48, g * Tlift ≠ -Tlift * g) ∧ -Tlift ∈ K48 ∧ IsProjOrder 4 (-Tlift) ∧ (∀ k ∈ K48, -k ∈ K48) := by
  decide


public theorem K48_star_trace_iff : ∀ k ∈ K48, star (tr2 k) = tr2 k ↔ ¬ IsProjOrder 4 k := by decide


public theorem K48_rows_nonvacuous :
    (∃ k ∈ K48, IsProjOrder 3 k ∧ tr2 k ≠ 0) ∧
    (∃ k ∈ K48, IsProjOrder 4 k ∧ tr2 k * tr2 k ≠ det2 k) ∧
    (∃ k ∈ K48, IsProjOrder 2 k ∧ tr2 k ≠ ⟨0, 1⟩ ∧ tr2 k ≠ ⟨0, -1⟩) ∧
    (∃ k ∈ K48, IsProjOrder 2 k ∧ det2 k = -1) ∧ (∃ k ∈ K48, IsProjOrder 2 k ∧ det2 k = 1) := by
  decide


public theorem K48_census :
    (K48.filter IsPM1).length = 2 ∧
    (K48.filter fun k => IsProjOrder 2 k ∧ det2 k = -1).length = 12 ∧
    (K48.filter fun k => IsProjOrder 2 k ∧ det2 k = 1).length = 6 ∧
    (K48.filter (IsProjOrder 3)).length = 16 ∧
    (K48.filter (IsProjOrder 4)).length = 12 ∧
    (K48.filter fun k => tr2 k = 0).length = 18 ∧ (K48.filter fun k => tr2 k = 1).length = 8 ∧
    (K48.filter fun k => tr2 k = -1).length = 8 ∧ (K48.filter fun k => tr2 k = ⟨0, 1⟩).length = 6 ∧
    (K48.filter fun k => tr2 k = ⟨0, -1⟩).length = 6 ∧ (K48.filter fun k => tr2 k = 2).length = 1 ∧
    (K48.filter fun k => tr2 k = -2).length = 1 := by
  decide


public theorem length_Q8 : Q8.length = 8 := by decide


public theorem Q8_projOrder : ∀ q ∈ Q8, IsPM1 q ∨ IsProjOrder 2 q := by decide


public theorem one_mem_Q8 : (1 : Mat) ∈ Q8 := by decide


public theorem Q8_mul_closed : ∀ a ∈ Q8, ∀ b ∈ Q8, a * b ∈ Q8 := by decide


public theorem Q8_mul_cube : ∀ q ∈ Q8, q * pw q 3 = 1 ∧ pw q 3 ∈ Q8 := by decide


public theorem Q8_normal : ∀ g ∈ K48, ∀ q ∈ Q8, ∃ q' ∈ Q8, g * q = q' * g := by decide


public theorem C4_sub_Q8 : ∀ c ∈ C4, c ∈ Q8 := by decide


public theorem C4_mul_closed : ∀ a ∈ C4, ∀ b ∈ C4, a * b ∈ C4 := by decide


public theorem length_C4 : C4.length = 4 ∧ C4.Nodup ∧ (Q8.filter fun q => q ∈ C4).length = 4 := by decide


public theorem C4_conj : ∀ x ∈ Q8, ∀ c ∈ C4, x * c * pw x 3 ∈ C4 ∧ (x ∉ C4 → x * c * pw x 3 = pw c 3) := by decide


public theorem psi_one : psi 1 = 1 := by decide


public theorem psi_mul : ∀ a ∈ C4, ∀ b ∈ C4, psi (a * b) = psi a * psi b := by decide


public theorem psi_faithful :
    psi (pw Tlift 2) = ⟨0, 1⟩ ∧ (⟨0, 1⟩ : GInt) * ⟨0, 1⟩ = -1 ∧ (∀ a ∈ C4, psi a = 1 → a = 1) ∧
    (C4.map psi = [1, ⟨0, 1⟩, -1, ⟨0, -1⟩]) := by
  decide


public theorem psi_ne_psi_conj : ∀ x ∈ Q8, x ∉ C4 → ∃ c ∈ C4, psi (x * c * pw x 3) ≠ psi c := by decide


public theorem indPsi_identity :
    ∀ g ∈ Q8, (tr2 g).im = 0 ∧ (indPsiNum g).im = 0 ∧ 4 * (tr2 g).re = (indPsiNum g).re := by decide


public theorem Q8_trace_values : ∀ g ∈ Q8, (g = 1 ∧ tr2 g = 2) ∨ (g = -1 ∧ tr2 g = -2) ∨ (¬ IsPM1 g ∧ tr2 g = 0) := by
  decide


public theorem length_P16 : P16.length = 16 := by decide


public theorem one_mem_P16 : (1 : Mat) ∈ P16 ∧ Tlift ∈ P16 ∧ Slift ∉ P16 := by decide


public theorem P16_mul_closed : ∀ a ∈ P16, ∀ b ∈ P16, a * b ∈ P16 := by decide


public theorem Q8_sub_P16 : ∀ q ∈ Q8, q ∈ P16 := by decide


public theorem cosets_partition : ((cosetReps.flatMap fun g => P16.map fun p => g * p).Perm K48) := by decide


public theorem fixedCosets_row_four : ∀ k ∈ K48, IsProjOrder 4 k → fixedCosets k = 1 := by decide


public theorem fixedCosets_row_three : ∀ k ∈ K48, IsProjOrder 3 k → fixedCosets k = 0 := by decide


public theorem fixedCosets_row_two_odd : ∀ k ∈ K48, IsProjOrder 2 k → det2 k = -1 → fixedCosets k = 1 := by decide


public theorem fixedCosets_row_two_even_and_central :
    ∀ k ∈ K48, (IsProjOrder 2 k → det2 k = 1 → fixedCosets k = 3) ∧ (IsPM1 k → fixedCosets k = 3) := by
  decide


public theorem isPM1_iff (A : Mat) : IsPM1 A ↔ A = 1 ∨ A = -1 := Iff.rfl


public theorem isProjOrder_iff (n : ℕ) (A : Mat) :
    IsProjOrder n A ↔ (A ^ n = 1 ∨ A ^ n = -1) ∧ ∀ m, 1 ≤ m → m < n → ¬ (A ^ m = 1 ∨ A ^ m = -1) := by
  unfold IsProjOrder IsPM1
  simp only [pw_eq_pow, List.mem_range'_1]
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨h, fun m h1 h2 => h' m ⟨h1, by omega⟩⟩
  · rintro ⟨h, h'⟩
    exact ⟨h, fun m hm => h' m hm.1 (by omega)⟩


public theorem trace_table (k : Mat) (hk : k ∈ Submonoid.closure ({Slift, Tlift} : Set Mat)) :
    (IsProjOrder 2 k → k.trace = 0) ∧
    (IsProjOrder 3 k → k.det = 1 ∧ k.trace ^ 2 = k.det) ∧
    (IsProjOrder 4 k → k.det = -1 ∧ (k.trace = ⟨0, 1⟩ ∨ k.trace = ⟨0, -1⟩)) := by
  rw [mem_closure_iff_mem_K48] at hk
  rw [← det2_eq_det, ← tr2_eq_trace]
  refine ⟨fun h2 => ?_, fun h3 => ?_, fun h4 => K48_row_four k hk h4⟩
  · rcases K48_det_cases k hk with hd | hd
    · exact (K48_row_two_even k hk h2 hd).1
    · exact K48_row_two_odd k hk h2 hd
  · obtain ⟨hd, ht⟩ := K48_row_three k hk h3
    exact ⟨hd, by rw [sq]; exact ht⟩


public theorem fixedCosets_table (k : Mat) (hk : k ∈ Submonoid.closure ({Slift, Tlift} : Set Mat)) :
    (IsProjOrder 4 k → fixedCosets k = 1) ∧ (IsProjOrder 3 k → fixedCosets k = 0) ∧
    (IsProjOrder 2 k → k.det = -1 → fixedCosets k = 1) ∧ (IsProjOrder 2 k → k.det = 1 → fixedCosets k = 3) ∧
    (IsPM1 k → fixedCosets k = 3) := by
  rw [mem_closure_iff_mem_K48] at hk
  rw [← det2_eq_det]
  exact ⟨fixedCosets_row_four k hk, fixedCosets_row_three k hk, fixedCosets_row_two_odd k hk,
    (fixedCosets_row_two_even_and_central k hk).1, (fixedCosets_row_two_even_and_central k hk).2⟩


public theorem trace_eq_indPsi (g : Mat) (hg : g ∈ Q8) :
    (g.trace).im = 0 ∧ (indPsiNum g).im = 0 ∧ 4 * (g.trace).re = (indPsiNum g).re := by
  rw [← tr2_eq_trace]; exact indPsi_identity g hg

section DetUniversal

variable {M : Type*} [CommGroup M]


public theorem Slift_mem_G48 : Slift ∈ G48 := Submonoid.subset_closure (by simp)


public theorem Tlift_mem_G48 : Tlift ∈ G48 := Submonoid.subset_closure (by simp)


public theorem Slift_comm_witness :
    Slift * Slift * (Tlift * Slift * Tlift * Tlift) = Tlift * Slift * Tlift * Tlift * Slift := by decide


public theorem Tlift_sq_comm_witness :
    Tlift * Tlift * (Slift * Tlift * Tlift) * Slift = Slift * (Slift * Tlift * Tlift) := by decide


public theorem hom_Slift_eq_one (φ : G48 →* M) : φ sG = 1 := by
  have h : sG * sG * (tG * sG * tG * tG) = tG * sG * tG * tG * sG := Subtype.ext Slift_comm_witness
  have h' := congrArg φ h
  simp only [map_mul] at h'
  have e : φ sG * (φ sG * φ sG * (φ tG * φ tG * φ tG)) = 1 * (φ sG * φ sG * (φ tG * φ tG * φ tG)) := by
    calc φ sG * (φ sG * φ sG * (φ tG * φ tG * φ tG))
          = φ sG * φ sG * (φ tG * φ sG * φ tG * φ tG) := by ac_rfl
      _ = φ tG * φ sG * φ tG * φ tG * φ sG := h'
      _ = 1 * (φ sG * φ sG * (φ tG * φ tG * φ tG)) := by rw [one_mul]; ac_rfl
  exact mul_right_cancel e


public theorem hom_Tlift_sq_eq_one (φ : G48 →* M) : φ tG * φ tG = 1 := by
  have h : tG * tG * (sG * tG * tG) * sG = sG * (sG * tG * tG) := Subtype.ext Tlift_sq_comm_witness
  have h' := congrArg φ h
  simp only [map_mul] at h'
  have e : φ tG * φ tG * (φ sG * φ sG * (φ tG * φ tG)) = 1 * (φ sG * φ sG * (φ tG * φ tG)) := by
    calc φ tG * φ tG * (φ sG * φ sG * (φ tG * φ tG))
          = φ tG * φ tG * (φ sG * φ tG * φ tG) * φ sG := by ac_rfl
      _ = φ sG * (φ sG * φ tG * φ tG) := h'
      _ = 1 * (φ sG * φ sG * (φ tG * φ tG)) := by rw [one_mul]; ac_rfl
  exact mul_right_cancel e


public theorem hom_evalWord (φ : G48 →* M) (hS : Slift.det = 1) (hT : Tlift.det = -1) (w : List (Fin 2)) :
    φ ⟨evalWord w, evalWord_mem_closure w⟩ = if (evalWord w).det = 1 then 1 else φ tG := by
  induction w with
  | nil =>
    have h1 : (⟨evalWord [], evalWord_mem_closure []⟩ : G48) = 1 := Subtype.ext rfl
    rw [h1, map_one, show evalWord [] = (1 : Mat) from rfl, Matrix.det_one, if_pos rfl]
  | cons a w ih =>
    have hdet : (evalWord w).det = 1 ∨ (evalWord w).det = -1 := by
      rw [← det2_eq_det]
      exact K48_det_cases _ ((mem_closure_iff_mem_K48 _).1 (evalWord_mem_closure w))
    have hne : (-1 : ℤ√(-2)) ≠ 1 := by decide
    match a with
    | 0 =>
      have h0 : (⟨evalWord (0 :: w), evalWord_mem_closure (0 :: w)⟩ : G48) =
          sG * ⟨evalWord w, evalWord_mem_closure w⟩ := Subtype.ext rfl
      rw [h0, map_mul, hom_Slift_eq_one, one_mul, ih, show evalWord (0 :: w) = Slift * evalWord w from rfl,
        Matrix.det_mul, hS, one_mul]
    | 1 =>
      have h0 : (⟨evalWord (1 :: w), evalWord_mem_closure (1 :: w)⟩ : G48) =
          tG * ⟨evalWord w, evalWord_mem_closure w⟩ := Subtype.ext rfl
      rw [h0, map_mul, ih, show evalWord (1 :: w) = Tlift * evalWord w from rfl, Matrix.det_mul, hT]
      rcases hdet with h | h
      · rw [h, if_pos rfl, mul_one, mul_one, if_neg hne]
      · rw [h, if_neg hne, neg_mul_neg, one_mul, if_pos rfl, hom_Tlift_sq_eq_one]


public theorem hom_factors_through_det (φ : G48 →* M) (hS : Slift.det = 1) (hT : Tlift.det = -1) (k : G48) :
    φ k = if (k : Mat).det = 1 then 1 else φ tG := by
  obtain ⟨k, hk⟩ := k
  have hK : k ∈ K48 := (mem_closure_iff_mem_K48 k).1 hk
  rw [K48_eq_map_evalWord] at hK
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hK
  exact hom_evalWord φ hS hT w


public theorem hom_eq_one_iff_det_eq_one (φ : G48 →* M) (hS : Slift.det = 1) (hT : Tlift.det = -1) (hφ : φ ≠ 1)
    (k : G48) : φ k = 1 ↔ (k : Mat).det = 1 := by
  have htG : φ tG ≠ 1 := fun h1 => hφ (MonoidHom.ext fun j => by
    rw [hom_factors_through_det φ hS hT j, h1, ite_self, MonoidHom.one_apply])
  rw [hom_factors_through_det φ hS hT k]
  constructor
  · intro h
    by_contra hd
    rw [if_neg hd] at h
    exact htG h
  · intro h
    rw [if_pos h]

end DetUniversal

end Matrix.Lift48
