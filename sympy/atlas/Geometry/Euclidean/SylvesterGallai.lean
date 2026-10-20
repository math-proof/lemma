/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/SylvesterGallai.lean -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

section
namespace MathlibExt.Geometry.Euclidean.SylvesterGallaiWanted

private lemma exists_same_side_pair (a b c : ℝ) : 0 ≤ a * b ∨ 0 ≤ a * c ∨ 0 ≤ b * c := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2, h3⟩ := h
  have hpos : 0 < (a * b) * (a * c) := mul_pos_of_neg_of_neg h1 h2
  have heq : (a * b) * (a * c) = a ^ 2 * (b * c) := by ring
  have hle : a ^ 2 * (b * c) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg a) (le_of_lt h3)
  linarith

private lemma key_inequality {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u d : V) (tX tY : ℝ) (hpos : 0 < ‖d‖) (hu : ‖u‖ = 1)
    (horth : inner ℝ d u = 0) (hprod : 0 ≤ tX * tY) (hle : tX ^ 2 ≤ tY ^ 2) :
    ∃ s0 : ℝ, ‖(tX • u - d) - s0 • (tY • u - d)‖ < ‖d‖ := by
  have hDpos : 0 < tY ^ 2 + ‖d‖ ^ 2 := by
    have h2 : 0 < ‖d‖ ^ 2 := pow_pos hpos 2
    linarith [sq_nonneg tY]
  have hDne : tY ^ 2 + ‖d‖ ^ 2 ≠ 0 := ne_of_gt hDpos
  have horth' : inner ℝ u d = 0 := (real_inner_comm d u).trans horth
  have habs : |tX| ≤ |tY| := sq_le_sq.mp hle
  have h1 : tX ^ 2 ≤ tX * tY := by
    have hmul : |tX| * |tX| ≤ |tX| * |tY| :=
      mul_le_mul_of_nonneg_left habs (abs_nonneg tX)
    have e1 : tX ^ 2 = |tX| * |tX| := by
      rw [← sq_abs tX, pow_two]
    have e2 : |tX| * |tY| = tX * tY := by
      rw [← abs_mul, abs_of_nonneg hprod]
    linarith
  refine ⟨(tX * tY + ‖d‖ ^ 2) / (tY ^ 2 + ‖d‖ ^ 2), ?_⟩
  set s0 := (tX * tY + ‖d‖ ^ 2) / (tY ^ 2 + ‖d‖ ^ 2) with hs0
  set A := tX - s0 * tY with hA
  set B := -(1 - s0) with hB
  have hexpr : (tX • u - d) - s0 • (tY • u - d) = A • u + B • d := by
    simp only [hA, hB]
    module
  have hinner : inner ℝ (A • u) (B • d) = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, horth', mul_zero, mul_zero]
  have hnorm1 : ‖A • u‖ ^ 2 = A ^ 2 := by
    rw [norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs]
  have hnorm2 : ‖B • d‖ ^ 2 = B ^ 2 * ‖d‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hsq : ‖A • u + B • d‖ ^ 2 = (tX - tY) ^ 2 * ‖d‖ ^ 2 / (tY ^ 2 + ‖d‖ ^ 2) := by
    have hpy : ‖A • u + B • d‖ ^ 2 = A ^ 2 + B ^ 2 * ‖d‖ ^ 2 := by
      have hns := norm_add_sq_real (A • u) (B • d)
      rw [hinner, hnorm1, hnorm2] at hns
      linarith
    rw [hpy]
    simp only [hA, hB, hs0]
    field_simp
    ring
  have hlt : (tX - tY) ^ 2 * ‖d‖ ^ 2 / (tY ^ 2 + ‖d‖ ^ 2) < ‖d‖ ^ 2 := by
    rw [div_lt_iff₀ hDpos]
    have hexpand : (tX - tY) ^ 2 = tX ^ 2 - 2 * (tX * tY) + tY ^ 2 := by ring
    have h2 : 0 < ‖d‖ ^ 2 := pow_pos hpos 2
    nlinarith [hexpand, h1, hprod, sq_nonneg tY, h2,
      mul_pos h2 (show 0 < tY ^ 2 + ‖d‖ ^ 2 from hDpos)]
  rw [hexpr]
  have hsq2 : ‖A • u + B • d‖ ^ 2 < ‖d‖ ^ 2 := by linarith [hsq, hlt]
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq2

/--
Every finite non-collinear subset of the real Euclidean plane determines an ordinary line: two
points of the set such that no third point of the set is collinear with them.
Source: J. J. Sylvester, Mathematical Question 11851, Educational Times 59 (1893) 98; L. M. Kelly, A
resolution of the Sylvester–Gallai problem, Discrete Comput. Geom. 1 (1986) 101–104 standard
real-plane version.

Proves `Wanted` entry `sylvester_gallai`.
-/
theorem sylvester_gallai
    (s : Set (EuclideanSpace ℝ (Fin 2)))
    (hs_fin : s.Finite)
    (hs_noncollinear : ¬Collinear ℝ s) :
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧
      ∀ c ∈ s, Collinear ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2))) → c = a ∨ c = b := by
  obtain ⟨p1, hp1⟩ : s.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    apply hs_noncollinear
    rw [h]
    exact collinear_empty ℝ _
  obtain ⟨p2, hp2, hp2ne⟩ : ∃ p2 ∈ s, p2 ≠ p1 := by
    by_contra h
    push Not at h
    apply hs_noncollinear
    apply Collinear.subset _ (collinear_singleton ℝ p1)
    intro x hx
    simp only [Set.mem_singleton_iff]
    exact h x hx
  obtain ⟨p3, hp3, hp3off⟩ :
      ∃ p3 ∈ s, p3 ∉ affineSpan ℝ ({p1, p2} : Set ((EuclideanSpace ℝ (Fin 2)))) := by
    by_contra h
    push Not at h
    apply hs_noncollinear
    rw [collinear_iff_of_mem hp1]
    refine ⟨p2 -ᵥ p1, fun p hp => ?_⟩
    have hpmem : p ∈ affineSpan ℝ ({p1, p2} : Set ((EuclideanSpace ℝ (Fin 2)))) := h p hp
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hpmem
    obtain ⟨r, hr⟩ := hpmem
    exact ⟨r, by rw [AffineMap.lineMap_apply] at hr; exact hr.symm⟩
  have htri : ¬Collinear ℝ ({p1, p2, p3} : Set ((EuclideanSpace ℝ (Fin 2)))) := by
    intro hc
    apply hp3off
    exact Collinear.mem_affineSpan_of_mem_of_ne
        (s := ({p1, p2, p3} : Set ((EuclideanSpace ℝ (Fin 2)))))
      (p₁ := p1) (p₂ := p2) (p₃ := p3) hc (by simp) (by simp) (by simp) (Ne.symm hp2ne)
  set T : Set ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)) ×
      (EuclideanSpace ℝ (Fin 2))) := {t | t.1 ∈ s ∧ t.2.1 ∈ s ∧ t.2.2 ∈ s ∧
    ¬Collinear ℝ ({t.1, t.2.1, t.2.2} : Set (EuclideanSpace ℝ (Fin 2)))} with hTdef
  set f : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)) →
      ℝ := fun t =>
    Metric.infDist t.1 ↑(affineSpan ℝ ({t.2.1, t.2.2} : Set (EuclideanSpace ℝ (Fin 2)))) with hfdef
  have hsub : T ⊆ s ×ˢ s ×ˢ s := by
    intro t ht
    obtain ⟨h1, h2, h3, -⟩ := ht
    exact ⟨h1, h2, h3⟩
  have hTfin : T.Finite := (hs_fin.prod (hs_fin.prod hs_fin)).subset hsub
  have hTne : T.Nonempty := ⟨(p1, p2, p3), hp1, hp2, hp3, htri⟩
  obtain ⟨⟨P, A, B⟩, hmT, hmin⟩ := Set.exists_min_image T f hTfin hTne
  obtain ⟨hPs, hAs, hBs, hNBA⟩ := hmT
  have hAB : A ≠ B := ne₂₃_of_not_collinear hNBA
  refine ⟨A, hAs, B, hBs, hAB, ?_⟩
  intro c hcs hcoll
  by_contra hcon
  push Not at hcon
  obtain ⟨hcA, hcB⟩ := hcon
  set ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) := affineSpan ℝ
      ({A, B} : Set (EuclideanSpace ℝ (Fin 2))) with hℓdef
  have hAℓ : A ∈ ℓ := left_mem_affineSpan_pair ℝ A B
  have hBℓ : B ∈ ℓ := right_mem_affineSpan_pair ℝ A B
  have hcℓ : c ∈ ℓ :=
    Collinear.mem_affineSpan_of_mem_of_ne (s := ({A, B, c} : Set (EuclideanSpace ℝ (Fin 2))))
      (p₁ := A) (p₂ := B) (p₃ := c) hcoll (by simp) (by simp) (by simp) hAB
  have hPℓ : P ∉ ℓ := by
    intro hPm
    exact hNBA (collinear_triple_of_mem_affineSpan_pair hPm hAℓ hBℓ)
  have : Nonempty ↥ℓ := ⟨⟨A, hAℓ⟩⟩
  set Q : (EuclideanSpace ℝ (Fin 2)) := ↑(EuclideanGeometry.orthogonalProjection ℓ P) with hQdef
  have hQℓ : Q ∈ ℓ := EuclideanGeometry.orthogonalProjection_mem P
  have hdist : dist P Q = Metric.infDist P ↑ℓ :=
    EuclideanGeometry.dist_orthogonalProjection_eq_infDist ℓ P
  set hvec : (EuclideanSpace ℝ (Fin 2)) := P -ᵥ Q with hhvec
  have horth_mem : hvec ∈ Submodule.orthogonal ℓ.direction :=
    EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal ℓ P
  have hvec_ne : hvec ≠ 0 := by
    intro hz
    apply hPℓ
    have hPQ : P = Q := eq_of_vsub_eq_zero hz
    rw [hPQ]
    exact hQℓ
  have hpos : 0 < ‖hvec‖ := norm_pos_iff.mpr hvec_ne
  set w : (EuclideanSpace ℝ (Fin 2)) := B -ᵥ A with hwdef
  have hw_ne : w ≠ 0 := vsub_ne_zero.mpr (Ne.symm hAB)
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw_ne
  set u : (EuclideanSpace ℝ (Fin 2)) := ‖w‖⁻¹ • w with hudef
  have hu_norm : ‖u‖ = 1 := by
    rw [hudef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn),
      inv_mul_cancel₀ (ne_of_gt hn)]
  have hdir : ℓ.direction = ℝ ∙ w := by
    have e1 : ℓ.direction = ℝ ∙ (A -ᵥ B) := by
      rw [hℓdef, direction_affineSpan, vectorSpan_pair]
    have e2 : (ℝ ∙ (A -ᵥ B) : Submodule ℝ (EuclideanSpace ℝ (Fin 2))) = ℝ ∙ (B -ᵥ A) := by
      have hneg : A -ᵥ B = -(B -ᵥ A) := by
        have hadd : (A -ᵥ B) + (B -ᵥ A) = 0 := by
          rw [vsub_add_vsub_cancel, vsub_self]
        exact eq_neg_of_add_eq_zero_left hadd
      rw [hneg]
      ext y
      simp only [Submodule.mem_span_singleton]
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨-a, by rw [neg_smul, ← smul_neg]⟩
      · rintro ⟨a, rfl⟩
        exact ⟨-a, by rw [neg_smul, smul_neg, neg_neg]⟩
    rw [e1, e2, ← hwdef]
  have hu_mem : u ∈ ℓ.direction := by
    rw [hdir]
    exact Submodule.mem_span_singleton.mpr ⟨‖w‖⁻¹, rfl⟩
  have horth : inner ℝ hvec u = 0 := by
    have h0 := Submodule.inner_right_of_mem_orthogonal hu_mem horth_mem
    have hcomm := real_inner_comm hvec u
    linarith
  have coord : ∀ X : (EuclideanSpace ℝ (Fin 2)), X ∈ ℓ → ∃ t : ℝ, X -ᵥ Q = t • u := by
    intro X hX
    have hmem : X -ᵥ Q ∈ ℓ.direction := AffineSubspace.vsub_mem_direction hX hQℓ
    rw [hdir] at hmem
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
    refine ⟨r * ‖w‖, ?_⟩
    have hwu : w = ‖w‖ • u := by
      rw [hudef, ← mul_smul, mul_inv_cancel₀ (ne_of_gt hn), one_smul]
    rw [mul_smul, ← hwu]
    exact hr.symm
  have step : ∀ X Y : (EuclideanSpace ℝ (Fin 2)), ∀ tX tY : ℝ, X ∈ s → Y ∈ s → X ∈ ℓ → Y ∈ ℓ →
      X ≠ Y → X -ᵥ Q = tX • u → Y -ᵥ Q = tY • u →
      0 ≤ tX * tY → tX ^ 2 ≤ tY ^ 2 → False := by
    intro X Y tX tY hXs hYs hXℓ hYℓ hXY hXc hYc hprod hle
    have hXPY : ¬Collinear ℝ ({X, P, Y} : Set (EuclideanSpace ℝ (Fin 2))) := by
      intro hc
      have hPXY : P ∈ affineSpan ℝ ({X, Y} : Set (EuclideanSpace ℝ (Fin 2))) :=
        Collinear.mem_affineSpan_of_mem_of_ne (s := ({X, P, Y} : Set (EuclideanSpace ℝ (Fin 2))))
          (p₁ := X) (p₂ := Y) (p₃ := P) hc (by simp) (by simp) (by simp) hXY
      have hsub : affineSpan ℝ ({X, Y} : Set (EuclideanSpace ℝ (Fin 2))) ≤ ℓ := by
        rw [affineSpan_le]
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact hXℓ
        · exact hYℓ
      exact hPℓ (hsub hPXY)
    have hmemT : (X, P, Y) ∈ T := ⟨hXs, hPs, hYs, hXPY⟩
    have hminXY : f (P, A, B) ≤ f (X, P, Y) := hmin _ hmemT
    obtain ⟨s0, hs0⟩ := key_inequality u hvec tX tY hpos hu_norm horth hprod hle
    have hFmem : AffineMap.lineMap P Y s0 ∈ affineSpan ℝ
        ({P, Y} : Set (EuclideanSpace ℝ (Fin 2))) :=
      AffineMap.lineMap_mem_affineSpan_pair s0 P Y
    have hbound : Metric.infDist X ↑(affineSpan ℝ ({P, Y} : Set (EuclideanSpace ℝ (Fin 2)))) ≤
        dist X (AffineMap.lineMap P Y s0) :=
      Metric.infDist_le_dist_of_mem hFmem
    have hF : AffineMap.lineMap P Y s0 -ᵥ P = s0 • (Y -ᵥ P) := by
      rw [AffineMap.lineMap_apply, vadd_vsub]
    have hXP : X -ᵥ P = tX • u - hvec := by
      have h1 := vsub_sub_vsub_cancel_right X P Q
      rw [hXc, ← hhvec] at h1
      exact h1.symm
    have hYP : Y -ᵥ P = tY • u - hvec := by
      have h1 := vsub_sub_vsub_cancel_right Y P Q
      rw [hYc, ← hhvec] at h1
      exact h1.symm
    have hXF : X -ᵥ (AffineMap.lineMap P Y s0) =
        (tX • u - hvec) - s0 • (tY • u - hvec) := by
      have h2 := vsub_sub_vsub_cancel_right X (AffineMap.lineMap P Y s0) P
      rw [hXP, hF, hYP] at h2
      exact h2.symm
    have hdistlt : dist X (AffineMap.lineMap P Y s0) < Metric.infDist P ↑ℓ := by
      have e1 : dist X (AffineMap.lineMap P Y s0) =
          ‖(tX • u - hvec) - s0 • (tY • u - hvec)‖ := by
        rw [dist_eq_norm_vsub (EuclideanSpace ℝ (Fin 2)) X (AffineMap.lineMap P Y s0), hXF]
      have e2 : Metric.infDist P ↑ℓ = ‖hvec‖ := by
        rw [← hdist, dist_eq_norm_vsub (EuclideanSpace ℝ (Fin 2)) P Q, ← hhvec]
      rw [e1, e2]
      exact hs0
    have hle1 : Metric.infDist P ↑ℓ ≤
        Metric.infDist X ↑(affineSpan ℝ ({P, Y} : Set (EuclideanSpace ℝ (Fin 2)))) := by
      have h2 : Metric.infDist P ↑(affineSpan ℝ ({A, B} : Set (EuclideanSpace ℝ (Fin 2)))) ≤
          Metric.infDist X ↑(affineSpan ℝ ({P, Y} : Set (EuclideanSpace ℝ (Fin 2)))) := hminXY
      rw [hℓdef]
      exact h2
    linarith [hle1, hbound, hdistlt]
  obtain ⟨tA, htA⟩ := coord A hAℓ
  obtain ⟨tB, htB⟩ := coord B hBℓ
  obtain ⟨tc, htc⟩ := coord c hcℓ
  rcases exists_same_side_pair tA tB tc with hpair | hpair | hpair
  · rcases le_total (tA ^ 2) (tB ^ 2) with hleAB | hleAB
    · exact step A B tA tB hAs hBs hAℓ hBℓ hAB htA htB hpair hleAB
    · exact step B A tB tA hBs hAs hBℓ hAℓ (Ne.symm hAB) htB htA
        (by rw [mul_comm]; exact hpair) hleAB
  · rcases le_total (tA ^ 2) (tc ^ 2) with hleAC | hleAC
    · exact step A c tA tc hAs hcs hAℓ hcℓ (Ne.symm hcA) htA htc hpair hleAC
    · exact step c A tc tA hcs hAs hcℓ hAℓ hcA htc htA
        (by rw [mul_comm]; exact hpair) hleAC
  · rcases le_total (tB ^ 2) (tc ^ 2) with hleBC | hleBC
    · exact step B c tB tc hBs hcs hBℓ hcℓ (Ne.symm hcB) htB htc hpair hleBC
    · exact step c B tc tB hcs hBs hcℓ hBℓ hcB htc htB
        (by rw [mul_comm]; exact hpair) hleBC

end MathlibExt.Geometry.Euclidean.SylvesterGallaiWanted
