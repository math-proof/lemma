import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProjectionTheory.code.SzemerediTrotter.Part2
open Finset Real SzemerediTrotter ProjectionTheory


namespace SzemerediTrotter

/--
[two_points_unique_line](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SzemerediTrotter.lean)
-/
@[path]
lemma two_points_unique_line
  {p q : Fin 2 → ℝ}
  {ℓ₁ ℓ₂ : Line2}
-- given
  (hpq : p ≠ q)
  (hp1 : p ∈ ℓ₁)
  (hq1 : q ∈ ℓ₁)
  (hp2 : p ∈ ℓ₂)
  (hq2 : q ∈ ℓ₂) :
-- imply
  ℓ₁.carrier = ℓ₂.carrier := by
-- proof
  have hspan_le1 : affineSpan ℝ {p, q} ≤ ℓ₁.carrier :=
    affineSpan_pair_le_of_mem_of_mem hp1 hq1
  have hspan_le2 : affineSpan ℝ {p, q} ≤ ℓ₂.carrier :=
    affineSpan_pair_le_of_mem_of_mem hp2 hq2
  have hne : p -ᵥ q ≠ (0 : Fin 2 → ℝ) := vsub_ne_zero.mpr hpq
  have hfinrank_span : Module.finrank ℝ (affineSpan ℝ ({p, q} : Set (Fin 2 → ℝ))).direction = 1 := by
    rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton hne]
  have hnonempty : (affineSpan ℝ ({p, q} : Set (Fin 2 → ℝ)) : Set (Fin 2 → ℝ)).Nonempty :=
    ⟨p, subset_affineSpan ℝ _ (Set.mem_insert p {q})⟩
  have hdir_eq1 : (affineSpan ℝ ({p, q} : Set (Fin 2 → ℝ))).direction = ℓ₁.carrier.direction := by
    have h_le := AffineSubspace.direction_le hspan_le1
    exact le_antisymm h_le (Submodule.eq_of_le_of_finrank_le h_le
      (by rw [hfinrank_span, ℓ₁.dim_eq])).ge
  have h1 := AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir_eq1 hnonempty hspan_le1
  have hdir_eq2 : (affineSpan ℝ ({p, q} : Set (Fin 2 → ℝ))).direction = ℓ₂.carrier.direction := by
    have h_le := AffineSubspace.direction_le hspan_le2
    exact le_antisymm h_le (Submodule.eq_of_le_of_finrank_le h_le
      (by rw [hfinrank_span, ℓ₂.dim_eq])).ge
  have h2 := AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir_eq2 hnonempty hspan_le2
  rw [← h1, ← h2]

end SzemerediTrotter

namespace SzemerediTrotter

/--
[Line2.ext'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SzemerediTrotter.lean)
-/
@[path]
lemma Line2.ext'
  {ℓ₁ ℓ₂ : Line2}
-- given
  (h : ℓ₁.carrier = ℓ₂.carrier) :
-- imply
  ℓ₁ = ℓ₂ := by
-- proof
  cases ℓ₁; cases ℓ₂; simp at h; subst h; rfl

end SzemerediTrotter

namespace SzemerediTrotter

/--
[weak_bound_incidence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SzemerediTrotter.lean)
-/
@[path]
lemma weak_bound_incidence
  {X : Finset (Fin 2 → ℝ)}
  {L : Finset Line2} :
-- imply
  (incidenceCount X L : ℝ) ≤ (X.card : ℝ) * (L.card : ℝ) ^ ((1 : ℝ) / 2) + (L.card : ℝ) := by
-- proof
  classical
  have hI_eq : incidenceCount X L = ∑ l ∈ L, (X.filter (fun x => x ∈ l)).card := by
    unfold incidenceCount; simp only [Finset.card_filter]; rw [← Finset.sum_product_right']
  have hsum_sq : ∑ l ∈ L, (X.filter (fun x => x ∈ l)).card ^ 2 =
    incidenceCount X L + ∑ l ∈ L, ((X.filter (fun x => x ∈ l)).card *
      ((X.filter (fun x => x ∈ l)).card - 1)) := by
    rw [hI_eq, ← Finset.sum_add_distrib]
    congr 1; ext l
    have : ∀ n : ℕ, n ^ 2 = n + n * (n - 1) := by
      intro n; cases n with
      | zero => simp
      | succ m => simp; ring
    exact this _
  have hoff_eq : ∀ l ∈ L, (X.filter (fun x => x ∈ l)).card *
    ((X.filter (fun x => x ∈ l)).card - 1) =
    (X.filter (fun x => x ∈ l)).offDiag.card := by
    intro l _
    rw [Finset.offDiag_card, Nat.mul_sub_one]
  have hoff_bound : ∑ l ∈ L, (X.filter (fun x => x ∈ l)).offDiag.card ≤ X.offDiag.card := by
    let A : Line2 → Finset ((Fin 2 → ℝ) × (Fin 2 → ℝ)) :=
      fun l => (X.filter (fun x => x ∈ l)).offDiag
    have hpd : Set.PairwiseDisjoint (↑L : Set Line2) A := by
      intro l₁ _ l₂ _ hne
      simp only [Function.onFun, A]
      rw [Finset.disjoint_left]
      intro ⟨p, q⟩ hp hq
      simp only [Finset.mem_offDiag, Finset.mem_filter] at hp hq
      exact absurd (Line2.ext' l₁ l₂
        (two_points_unique_line p q hp.2.2 l₁ l₂ hp.1.2 hp.2.1.2 hq.1.2 hq.2.1.2)) hne
    have hsub : ∀ l ∈ L, A l ⊆ X.offDiag := by
      intro l _ ⟨p, q⟩ hp
      simp only [A, Finset.mem_offDiag, Finset.mem_filter] at hp ⊢
      exact ⟨hp.1.1, hp.2.1.1, hp.2.2⟩
    calc ∑ l ∈ L, (A l).card
      = (L.biUnion A).card := (Finset.card_biUnion hpd).symm
      _ ≤ X.offDiag.card := Finset.card_le_card (Finset.biUnion_subset.mpr hsub)
  have hXoff : X.offDiag.card ≤ X.card ^ 2 := by
    rw [Finset.offDiag_card, sq]; omega
  have hsum_sq_bound : (∑ l ∈ L, (X.filter (fun x => x ∈ l)).card ^ 2 : ℕ) ≤
    incidenceCount X L + X.card ^ 2 := by
    rw [hsum_sq]
    gcongr
    calc ∑ l ∈ L, ((X.filter (fun x => x ∈ l)).card *
      ((X.filter (fun x => x ∈ l)).card - 1))
      = ∑ l ∈ L, (X.filter (fun x => x ∈ l)).offDiag.card :=
        Finset.sum_congr rfl hoff_eq
      _ ≤ X.offDiag.card := hoff_bound
      _ ≤ X.card ^ 2 := hXoff
  have hCS : (∑ l ∈ L, ((X.filter (fun x => x ∈ l)).card : ℝ)) ^ 2 ≤
    (L.card : ℝ) * ∑ l ∈ L, (((X.filter (fun x => x ∈ l)).card : ℝ)) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hI_cast : (∑ l ∈ L, ((X.filter (fun x => x ∈ l)).card : ℝ)) =
    (incidenceCount X L : ℝ) := by
    rw [hI_eq]; push_cast; rfl
  have hI_sq : (incidenceCount X L : ℝ) ^ 2 ≤
    (L.card : ℝ) * ((incidenceCount X L : ℝ) + (X.card : ℝ) ^ 2) := by
    calc (incidenceCount X L : ℝ) ^ 2
      = (∑ l ∈ L, ((X.filter (fun x => x ∈ l)).card : ℝ)) ^ 2 := by rw [hI_cast]
      _ ≤ (L.card : ℝ) * ∑ l ∈ L, (((X.filter (fun x => x ∈ l)).card : ℝ)) ^ 2 := hCS
      _ ≤ (L.card : ℝ) * ((incidenceCount X L : ℝ) + (X.card : ℝ) ^ 2) := by
        gcongr; exact_mod_cast hsum_sq_bound
  rw [← Real.sqrt_eq_rpow]
  set I := (incidenceCount X L : ℝ)
  set Lc := (L.card : ℝ)
  set Xc := (X.card : ℝ)
  have hLc_nn : Lc ≥ 0 := by positivity
  have hXc_nn : Xc ≥ 0 := by positivity
  have h_ineq : I ^ 2 ≤ Lc * Xc ^ 2 + Lc * I := by linarith [hI_sq]
  by_contra hlt
  push Not at hlt
  have hsqrt : Real.sqrt Lc * Real.sqrt Lc = Lc := Real.mul_self_sqrt hLc_nn
  have h1 : I * (I - Lc) ≤ Lc * Xc ^ 2 := by nlinarith
  have hIL : I - Lc > Xc * Real.sqrt Lc := by linarith
  have hXsL_nn : Xc * Real.sqrt Lc ≥ 0 := mul_nonneg hXc_nn (Real.sqrt_nonneg Lc)
  have h2 : I * (I - Lc) > (Xc * Real.sqrt Lc + Lc) * (Xc * Real.sqrt Lc) := by
    nlinarith [hlt, hIL, hXsL_nn]
  have h3 : (Xc * Real.sqrt Lc + Lc) * (Xc * Real.sqrt Lc) ≥ Lc * Xc ^ 2 := by
    nlinarith [hsqrt, hXsL_nn, mul_nonneg hLc_nn hXsL_nn]
  linarith

end SzemerediTrotter

namespace SzemerediTrotter

/--
[incidence_ge_R_mul_rRichLines](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SzemerediTrotter.lean)
-/
@[path]
lemma incidence_ge_R_mul_rRichLines
  {X : Finset (Fin 2 → ℝ)}
  {L : Finset Line2}
  {R : ℕ} :
-- imply
  R * (rRichLines X L R).card ≤ incidenceCount X (rRichLines X L R) := by
-- proof
  classical
  have hI_eq : incidenceCount X (rRichLines X L R) =
    ∑ l ∈ (rRichLines X L R), (X.filter (fun x => x ∈ l)).card := by
    unfold incidenceCount
    simp only [Finset.card_filter]
    rw [← Finset.sum_product_right']
  rw [hI_eq]
  have h : ∀ l ∈ rRichLines X L R, R ≤ (X.filter (fun x => x ∈ l)).card := by
    intro l hl; simp only [rRichLines, Finset.mem_filter] at hl; exact hl.2
  calc R * (rRichLines X L R).card
    = ∑ _l ∈ rRichLines X L R, R := by rw [Finset.sum_const]; ring
    _ ≤ ∑ l ∈ rRichLines X L R, (X.filter (fun x => x ∈ l)).card :=
      Finset.sum_le_sum h
set_option maxHeartbeats 800000 in

end SzemerediTrotter

namespace ProjectionTheory

/--
[mem_mkProjLine_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SzemerediTrotter.lean)
-/
@[path]
lemma mem_mkProjLine_iff
  {θ : ℝ}
  {p₀ q : Fin 2 → ℝ}
-- given
  (hθ : 0 ≤ θ ∧ θ < Real.pi) :
-- imply
  q ∈ (mkProjLine θ hθ p₀).carrier ↔ projR2 θ q = projR2 θ p₀ := by
-- proof
  simp only [mkProjLine, AffineSubspace.mem_mk', LinearMap.mem_ker,
    projR2Lin, LinearMap.coe_mk, AddHom.coe_mk, projR2, Pi.sub_apply, vsub_eq_sub]
  constructor <;> intro h <;> linarith

end ProjectionTheory

namespace ProjectionTheory

/--
[mkProjLine_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SzemerediTrotter.lean)
-/
@[path]
lemma mkProjLine_eq_iff
  {θ : ℝ}
  {p₀ q₀ : Fin 2 → ℝ}
-- given
  (hθ : 0 ≤ θ ∧ θ < Real.pi) :
-- imply
  mkProjLine θ hθ p₀ = mkProjLine θ hθ q₀ ↔ projR2 θ p₀ = projR2 θ q₀ := by
-- proof
  constructor
  · intro h
    have hq : q₀ ∈ (mkProjLine θ hθ p₀).carrier := by
      rw [h]; exact (mem_mkProjLine_iff θ hθ q₀ q₀).mpr rfl
    exact ((mem_mkProjLine_iff θ hθ p₀ q₀).mp hq).symm
  · intro h
    suffices h_carrier : (mkProjLine θ hθ p₀).carrier = (mkProjLine θ hθ q₀).carrier by
      exact match mkProjLine θ hθ p₀, mkProjLine θ hθ q₀, h_carrier with
      | ⟨c₁, d₁, n₁⟩, ⟨c₂, d₂, n₂⟩, hc => by simp_all
    simp only [mkProjLine]
    have hvsub : q₀ -ᵥ p₀ ∈ LinearMap.ker (projR2Lin θ) := by
      simp only [LinearMap.mem_ker, projR2Lin, LinearMap.coe_mk, AddHom.coe_mk,
        projR2, vsub_eq_sub, Pi.sub_apply]
      have : projR2 θ q₀ - projR2 θ p₀ =
        (q₀ 0 - p₀ 0) * Real.cos θ + (q₀ 1 - p₀ 1) * Real.sin θ := by
        simp [projR2]; ring
      linarith [this]
    have hq_in_p : q₀ ∈ (AffineSubspace.mk' p₀ (LinearMap.ker (projR2Lin θ)) :
      AffineSubspace ℝ (Fin 2 → ℝ)) := by
      rw [AffineSubspace.mem_mk']; exact hvsub
    calc AffineSubspace.mk' p₀ (LinearMap.ker (projR2Lin θ))
      = AffineSubspace.mk' q₀
        (AffineSubspace.mk' p₀ (LinearMap.ker (projR2Lin θ))).direction :=
        (AffineSubspace.mk'_eq hq_in_p).symm
      _ = AffineSubspace.mk' q₀ (LinearMap.ker (projR2Lin θ)) := by
        rw [AffineSubspace.direction_mk']

end ProjectionTheory

namespace ProjectionTheory

/--
[card_image_le_of_eq_imp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SzemerediTrotter.lean)
-/
@[path]
lemma card_image_le_of_eq_imp
  [DecidableEq β]
  [DecidableEq γ]
  {s : Finset α}
  {f : α → β}
  {g : α → γ}
-- given
  (h : ∀ a₁ ∈ s, ∀ a₂ ∈ s, g a₁ = g a₂ → f a₁ = f a₂)
  (hs : s.Nonempty) :
-- imply
  (s.image f).card ≤ (s.image g).card := by
-- proof
  classical
  obtain ⟨a₀, ha₀⟩ := hs
  let φ : γ → β := fun c => if hc : ∃ a ∈ s, g a = c then f hc.choose else f a₀
  suffices hsub : s.image f ⊆ (s.image g).image φ by
    calc (s.image f).card ≤ ((s.image g).image φ).card := Finset.card_le_card hsub
      _ ≤ (s.image g).card := Finset.card_image_le
  intro b hb
  obtain ⟨a, ha_s, ha_f⟩ := Finset.mem_image.mp hb
  rw [Finset.mem_image]
  refine ⟨g a, Finset.mem_image.mpr ⟨a, ha_s, rfl⟩, ?_⟩
  show φ (g a) = b
  simp only [φ]
  have hex : ∃ a' ∈ s, g a' = g a := ⟨a, ha_s, rfl⟩
  rw [dif_pos hex]
  have := h _ hex.choose_spec.1 _ ha_s hex.choose_spec.2
  rw [this, ha_f]
set_option maxHeartbeats 400000 in

end ProjectionTheory

namespace ProjectionTheory

/--
[proj_bound_of_st_ineq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SzemerediTrotter.lean)
-/
@[path]
lemma proj_bound_of_st_ineq
  {Xr Sr Dr : ℝ}
-- given
  (hXr : Xr > 0)
  (hSr : Sr ≥ 1)
  (hDr : Dr ≥ 2)
  (h2S : 2 * Sr < Xr)
  (hST : Xr * Dr ≤ Xr + Sr * Dr + Xr ^ ((2 : ℝ) / 3) * (Sr * Dr) ^ ((2 : ℝ) / 3)) :
-- imply
  Dr ≤ 144 * Sr ^ 2 * Xr⁻¹ + 1 := by
-- proof
  have hDr_pos : Dr > 0 := by linarith
  have hSr_pos : Sr > 0 := by linarith
  have hSDr_pos : Sr * Dr > 0 := mul_pos hSr_pos hDr_pos
  have hSDr_nn : Sr * Dr ≥ 0 := hSDr_pos.le
  have h_cube_R : (Xr ^ ((2:ℝ)/3) * (Sr * Dr) ^ ((2:ℝ)/3)) ^ 3 = Xr ^ 2 * (Sr * Dr) ^ 2 := by
    rw [mul_pow, ← Real.rpow_natCast (Xr ^ ((2:ℝ)/3)) 3, ← Real.rpow_mul hXr.le]
    norm_num
    rw [← Real.rpow_natCast ((Sr * Dr) ^ ((2:ℝ)/3)) 3, ← Real.rpow_mul hSDr_nn]
    norm_num
  have hR_nn : Xr ^ ((2:ℝ)/3) * (Sr * Dr) ^ ((2:ℝ)/3) ≥ 0 :=
    mul_nonneg (Real.rpow_nonneg hXr.le _) (Real.rpow_nonneg hSDr_nn _)
  have hXm2S_le_R : Xr - 2 * Sr ≤ Xr ^ ((2:ℝ)/3) * (Sr * Dr) ^ ((2:ℝ)/3) := by nlinarith
  have hXm2S_pos : Xr - 2 * Sr > 0 := by linarith
  have h_cube_exp : (Xr - 2 * Sr) ^ 3 ≤ Xr ^ 2 * Sr ^ 2 * Dr ^ 2 :=
    calc (Xr - 2 * Sr) ^ 3
      ≤ (Xr ^ ((2:ℝ)/3) * (Sr * Dr) ^ ((2:ℝ)/3)) ^ 3 :=
        pow_le_pow_left₀ hXm2S_pos.le hXm2S_le_R 3
      _ = Xr ^ 2 * (Sr * Dr) ^ 2 := h_cube_R
      _ = Xr ^ 2 * Sr ^ 2 * Dr ^ 2 := by ring
  have hR_bound : Xr * (Dr - 2) / 2 ≤ Xr ^ ((2:ℝ)/3) * (Sr * Dr) ^ ((2:ℝ)/3) := by nlinarith
  have hLHS_nn : Xr * (Dr - 2) / 2 ≥ 0 :=
    div_nonneg (mul_nonneg hXr.le (by linarith : Dr - 2 ≥ 0)) (by norm_num : (2:ℝ) ≥ 0)
  have h_simp : Xr * (Dr - 2) ^ 3 ≤ 8 * Sr ^ 2 * Dr ^ 2 := by
    have h_cubed : (Xr * (Dr - 2) / 2) ^ 3 ≤ Xr ^ 2 * Sr ^ 2 * Dr ^ 2 :=
      calc (Xr * (Dr - 2) / 2) ^ 3
        ≤ (Xr ^ ((2:ℝ)/3) * (Sr * Dr) ^ ((2:ℝ)/3)) ^ 3 :=
          pow_le_pow_left₀ hLHS_nn hR_bound 3
        _ = Xr ^ 2 * (Sr * Dr) ^ 2 := h_cube_R
        _ = Xr ^ 2 * Sr ^ 2 * Dr ^ 2 := by ring
    have h_exp : (Xr * (Dr - 2) / 2) ^ 3 = Xr ^ 3 * (Dr - 2) ^ 3 / 8 := by ring
    have h1 : Xr ^ 3 * (Dr - 2) ^ 3 ≤ 8 * (Xr ^ 2 * Sr ^ 2 * Dr ^ 2) := by linarith [h_exp]
    have hXr2 : (0 : ℝ) < Xr ^ 2 := by positivity
    have h1' : Xr ^ 2 * (Xr * (Dr - 2) ^ 3) ≤ Xr ^ 2 * (8 * Sr ^ 2 * Dr ^ 2) := by
      ring_nf; ring_nf at h1; linarith
    linarith [le_of_mul_le_mul_of_pos_left h1' hXr2]
  suffices h : (Dr - 1) * Xr ≤ 144 * Sr ^ 2 by
    nlinarith [mul_inv_cancel₀ (ne_of_gt hXr), inv_pos.mpr hXr]
  by_cases hDr4 : Dr ≥ 4
  · have h1 : (Dr / 2) ^ 3 ≤ (Dr - 2) ^ 3 :=
    pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ Dr / 2) (by linarith : Dr / 2 ≤ Dr - 2) 3
    have h5 : Xr * Dr ≤ 64 * Sr ^ 2 := by
      have hDr2_pos : Dr ^ 2 > 0 := by positivity
      nlinarith [h1, h_simp]
    nlinarith
  · simp only [not_le] at hDr4
    have h_cube_small : (Xr - 2 * Sr) ^ 3 ≤ 16 * Sr ^ 2 * Xr ^ 2 := by
      have hDr2 : Dr ^ 2 < 16 := by nlinarith [sq_nonneg (4 - Dr)]
      nlinarith [sq_nonneg (Xr * Sr)]
    by_contra h_neg
    simp only [not_le] at h_neg
    have hXr_large : Xr > 48 * Sr ^ 2 := by nlinarith
    have h4 : 2 * Sr < Xr / 24 := by nlinarith [sq_nonneg (Sr - 1)]
    have h6 : (23 * Xr / 24) ^ 3 ≤ 16 * Sr ^ 2 * Xr ^ 2 :=
      calc (23 * Xr / 24) ^ 3
        ≤ (Xr - 2 * Sr) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
        _ ≤ 16 * Sr ^ 2 * Xr ^ 2 := h_cube_small
    have h_exp6 : (23 * Xr / 24) ^ 3 = 12167 * Xr ^ 3 / 13824 := by ring
    have h7 : 12167 * Xr ^ 3 ≤ 221184 * Sr ^ 2 * Xr ^ 2 := by nlinarith [h_exp6]
    have hXr2_pos : (0 : ℝ) < Xr ^ 2 := by positivity
    have h7' : Xr ^ 2 * (12167 * Xr) ≤ Xr ^ 2 * (221184 * Sr ^ 2) := by
      ring_nf; ring_nf at h7; linarith
    have h8 : 12167 * Xr ≤ 221184 * Sr ^ 2 :=
      le_of_mul_le_mul_of_pos_left h7' hXr2_pos
    nlinarith [sq_nonneg Sr]

end ProjectionTheory

namespace ProjectionTheory

/--
[fiber_lines_st_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SzemerediTrotter.lean)
-/
@[path]
lemma fiber_lines_st_bound
  {X : Finset (Fin 2 → ℝ)}
  {S : ℕ}
  {D : Finset ℝ}
-- given
  (hDr : ∀ θ ∈ D, 0 ≤ θ ∧ θ < Real.pi)
  (hSb : ∀ θ ∈ D, (projImageR2 θ X).card ≤ S)
  (hX : X.Nonempty) :
-- imply
  ∃ L : Finset SzemerediTrotter.Line2, L.card ≤ S * D.card ∧ X.card * D.card ≤ SzemerediTrotter.incidenceCount X L := by
-- proof
  classical
  let L : Finset SzemerediTrotter.Line2 :=
    D.biUnion (fun θ => if h : 0 ≤ θ ∧ θ < Real.pi then X.image (mkProjLine θ h) else ∅)
  refine ⟨L, ?_, ?_⟩
  ·
    calc L.card
      ≤ ∑ θ ∈ D, (if h : 0 ≤ θ ∧ θ < Real.pi
        then X.image (mkProjLine θ h) else ∅).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _θ ∈ D, S := by
        apply Finset.sum_le_sum
        intro θ hθD
        simp only [hDr θ hθD]
        calc (X.image (mkProjLine θ (hDr θ hθD))).card
          ≤ (X.image (projR2 θ)).card := by
            apply card_image_le_of_eq_imp X (mkProjLine θ (hDr θ hθD)) (projR2 θ)
            · intro a₁ _ a₂ _ heq
              exact (mkProjLine_eq_iff θ (hDr θ hθD) a₁ a₂).mpr heq
            · exact hX
          _ ≤ S := hSb θ hθD
      _ = S * D.card := by simp [Finset.sum_const, mul_comm]
  ·
    show X.card * D.card ≤ SzemerediTrotter.incidenceCount X L
    unfold SzemerediTrotter.incidenceCount
    rw [show X.card * D.card = (X ×ˢ D).card from (Finset.card_product X D).symm]
    let f : (Fin 2 → ℝ) × ℝ → (Fin 2 → ℝ) × SzemerediTrotter.Line2 :=
      fun p => if h : p.2 ∈ D then (p.1, mkProjLine p.2 (hDr p.2 h) p.1)
        else (p.1, mkProjLine 0 ⟨le_refl 0, Real.pi_pos⟩ p.1)
    apply Finset.card_le_card_of_injOn f
    ·
      intro p hp
      have hmem := Finset.mem_product.mp hp
      simp only [f, hmem.2, dite_true, Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hmem.1, Finset.mem_biUnion.mpr ⟨p.2, hmem.2,
        by simp [hDr p.2 hmem.2, Finset.mem_image]; exact ⟨p.1, hmem.1, rfl⟩⟩⟩,
        (mem_mkProjLine_iff p.2 (hDr p.2 hmem.2) p.1 p.1).mpr rfl⟩
    ·
      intro p₁ hp₁ p₂ hp₂ heq
      have hmem₁ := Finset.mem_product.mp hp₁
      have hmem₂ := Finset.mem_product.mp hp₂
      simp only [f, hmem₁.2, hmem₂.2, dite_true, Prod.mk.injEq] at heq
      have hx_eq := heq.1
      have hline_eq := heq.2
      have hcarr : (mkProjLine p₁.2 (hDr p₁.2 hmem₁.2) p₁.1).carrier =
        (mkProjLine p₂.2 (hDr p₂.2 hmem₂.2) p₂.1).carrier := congr_arg _ hline_eq
      simp only [mkProjLine] at hcarr
      rw [hx_eq] at hcarr
      have hdir : LinearMap.ker (projR2Lin p₁.2) = LinearMap.ker (projR2Lin p₂.2) := by
        have hd := AffineSubspace.direction_mk' p₂.1 (LinearMap.ker (projR2Lin p₁.2))
        rw [hcarr] at hd
        rw [← hd, AffineSubspace.direction_mk']
      have hv_ker1 : (![- Real.sin p₁.2, Real.cos p₁.2] : Fin 2 → ℝ) ∈
        LinearMap.ker (projR2Lin p₁.2) := by
        simp [LinearMap.mem_ker, projR2Lin, projR2, Matrix.cons_val_zero,
          Matrix.cons_val_one]; ring
      have hv_ker2 := hdir ▸ hv_ker1
      simp only [LinearMap.mem_ker, projR2Lin, projR2, LinearMap.coe_mk, AddHom.coe_mk,
        Matrix.cons_val_zero, Matrix.cons_val_one] at hv_ker2
      have hsin : Real.sin (p₂.2 - p₁.2) = 0 := by rw [Real.sin_sub]; linarith
      have hθ₁ := hDr p₁.2 hmem₁.2
      have hθ₂ := hDr p₂.2 hmem₂.2
      have hdiff := (Real.sin_eq_zero_iff_of_lt_of_lt
        (by linarith [hθ₁.1, hθ₁.2, hθ₂.1, hθ₂.2] : -Real.pi < p₂.2 - p₁.2)
        (by linarith [hθ₁.1, hθ₁.2, hθ₂.1, hθ₂.2] : p₂.2 - p₁.2 < Real.pi)).mp hsin
      exact Prod.ext hx_eq (by linarith)
set_option maxHeartbeats 800000 in
/-- **Szemerédi--Trotter projection theorem.** There exists a universal constant $C > 0$
such that for any finite point set $X \subset \mathbb{R}^2$, set of directions
$D \subset [0, \pi)$, and bound $|\pi_\theta(X)| \le S$ for $\theta \in D$, if $2S < |X|$
then $|D| \le C \cdot S^2 / |X| + 1$. -/

end ProjectionTheory

/--
[projR2Lin_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SzemerediTrotter.lean)
-/
@[path]
private lemma projR2Lin_surjective_eq
  {θ : ℝ} :
-- imply
  Function.Surjective (projR2Lin θ) := by
-- proof
  apply ProjectionTheory.projR2Lin_surjective θ

/--
[projR2Lin_ker_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SzemerediTrotter.lean)
-/
@[path]
private lemma projR2Lin_ker_finrank_eq
  {θ : ℝ}
-- given
  (hθ : 0 ≤ θ ∧ θ < Real.pi) :
-- imply
  Module.finrank ℝ (LinearMap.ker (projR2Lin θ)) = 1 := by
-- proof
  apply ProjectionTheory.projR2Lin_ker_finrank θ hθ


-- created on 2026-10-23
