/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.SetTheory.Cardinal.Free
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.MetricSpace.IsometricSMul
import Def.MeasureTheory.Geometry.BanachTarski.Part14


namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-- The axis never has vanishing outer coordinates. -/
theorem btU_nz_all (w : FreeGroup (Fin 2)) :
    ((btU w) 0, (btU w) 2) ≠ (0, 0) := by
  by_cases hw : w = 1
  · subst hw
    have eU : btU 1 = ![1, 0, (0 : ℝ)] := rfl
    have e0 : ((![1, 0, (0 : ℝ)] : Fin 3 → ℝ)) 0 = 1 := by
      simp [Matrix.cons_val_zero]
    have e2 : ((![1, 0, (0 : ℝ)] : Fin 3 → ℝ)) 2 = 0 := by
      simp [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    rw [eU, e0, e2]
    simp
  · exact btU_nz w hw

/-- Each bad-angle set for fixed data is countable. -/
theorem btBadAngle_countable (w v : FreeGroup (Fin 2)) (n : ℕ) (e : Bool)
    (hn : 1 ≤ n) :
    Set.Countable {t : ℝ |
      Matrix.mulVec (btRotY ((n : ℝ) * t) : Matrix (Fin 3) (Fin 3) ℝ) (btU w) =
        btEps e • btU v} := by
  by_cases hemp : ∃ t₁ : ℝ,
      Matrix.mulVec (btRotY ((n : ℝ) * t₁) : Matrix (Fin 3) (Fin 3) ℝ) (btU w) =
        btEps e • btU v
  · obtain ⟨t₁, ht₁⟩ := hemp
    have hsub : {t : ℝ |
          Matrix.mulVec (btRotY ((n : ℝ) * t) : Matrix (Fin 3) (Fin 3) ℝ) (btU w) =
            btEps e • btU v} ⊆
        Set.range (fun k : ℤ => t₁ + (k : ℝ) * (2 * Real.pi) / (n : ℝ)) := by
      intro t ht
      have hboth : Matrix.mulVec (btRotY ((n : ℝ) * t) : Matrix (Fin 3) (Fin 3) ℝ) (btU w) =
          Matrix.mulVec (btRotY ((n : ℝ) * t₁) : Matrix (Fin 3) (Fin 3) ℝ) (btU w) :=
        ht.trans ht₁.symm
      have hsplit : (n : ℝ) * t = (n : ℝ) * t₁ + (n : ℝ) * (t - t₁) := by ring
      have hmat : Matrix.mulVec (btRotY ((n : ℝ) * t) : Matrix (Fin 3) (Fin 3) ℝ) (btU w) =
          Matrix.mulVec (btRotY ((n : ℝ) * t₁) : Matrix (Fin 3) (Fin 3) ℝ)
            (Matrix.mulVec (btRotY ((n : ℝ) * (t - t₁)) : Matrix (Fin 3) (Fin 3) ℝ) (btU w)) := by
        rw [hsplit, btRotY_mulVec]
      rw [hmat] at hboth
      have hfix : Matrix.mulVec (btRotY ((n : ℝ) * (t - t₁)) : Matrix (Fin 3) (Fin 3) ℝ) (btU w) =
          btU w :=
        btRotY_inj _ _ _ hboth
      have hcos : Real.cos ((n : ℝ) * (t - t₁)) = 1 :=
        btRotY_fix_cos _ _ hfix (btU_nz_all w)
      obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).mp hcos
      have hnR : (n : ℝ) ≠ 0 := by
        have hn0 : n ≠ 0 := by omega
        exact_mod_cast hn0
      have htt : t - t₁ = (k : ℝ) * (2 * Real.pi) / (n : ℝ) := by
        rw [eq_div_iff hnR, mul_comm]
        exact hk.symm
      have htt2 : t = t₁ + (k : ℝ) * (2 * Real.pi) / (n : ℝ) := by
        rw [← htt]
        abel
      exact ⟨k, htt2.symm⟩
    exact Set.Countable.mono hsub (Set.countable_range _)
  · rw [Set.eq_empty_of_forall_notMem (fun t ht => hemp ⟨t, ht⟩)]
    exact Set.countable_empty

/-- The bad-angle set with side conditions is countable. -/
theorem btBadAngle_piece (w v : FreeGroup (Fin 2)) (n : ℕ) (e : Bool) :
    Set.Countable {t : ℝ | w ≠ 1 ∧ v ≠ 1 ∧ 1 ≤ n ∧
      Matrix.mulVec (btRotY ((n : ℝ) * t) : Matrix (Fin 3) (Fin 3) ℝ) (btU w) =
        btEps e • btU v} := by
  by_cases hn : 1 ≤ n
  · exact Set.Countable.mono (fun t ht => ht.2.2.2) (btBadAngle_countable w v n e hn)
  · have hemp : {t : ℝ | w ≠ 1 ∧ v ≠ 1 ∧ 1 ≤ n ∧
        Matrix.mulVec (btRotY ((n : ℝ) * t) : Matrix (Fin 3) (Fin 3) ℝ) (btU w) =
          btEps e • btU v} = ∅ :=
      Set.eq_empty_of_forall_notMem (fun t ht => hn ht.2.2.1)
    rw [hemp]
    exact Set.countable_empty

/-- There is an angle avoiding all axis alignments. -/
theorem btGoodAngle :
    ∃ t : ℝ, ∀ (w v : FreeGroup (Fin 2)), w ≠ 1 → v ≠ 1 → ∀ (n : ℕ), 1 ≤ n →
      ∀ (ε : ℝ), ε = 1 ∨ ε = -1 →
        Matrix.mulVec (btRotY (n * t) : Matrix (Fin 3) (Fin 3) ℝ) (btU w) ≠
          ε • btU v := by
  have hbad : Set.Countable (⋃ (w : FreeGroup (Fin 2)) (v : FreeGroup (Fin 2))
      (n : ℕ) (e : Bool), {t : ℝ | w ≠ 1 ∧ v ≠ 1 ∧ 1 ≤ n ∧
        Matrix.mulVec (btRotY ((n : ℝ) * t) : Matrix (Fin 3) (Fin 3) ℝ) (btU w) =
          btEps e • btU v}) :=
    Set.countable_iUnion fun w => Set.countable_iUnion fun v =>
      Set.countable_iUnion fun n => Set.countable_iUnion fun e =>
        btBadAngle_piece w v n e
  obtain ⟨t, ht⟩ := (hbad.dense_compl ℝ).nonempty
  refine ⟨t, ?_⟩
  intro w v hw hv n hn ε hε hcon
  apply ht
  simp only [Set.mem_iUnion]
  by_cases hε1 : ε = 1
  · refine ⟨w, v, n, true, hw, hv, hn, ?_⟩
    rw [hε1] at hcon
    exact hcon
  · have hεm : ε = -1 := Or.resolve_left hε hε1
    refine ⟨w, v, n, false, hw, hv, hn, ?_⟩
    rw [hεm] at hcon
    exact hcon

/-- The punctured ball is congruent to the free locus. -/
theorem btCongr_punctured_omega :
    btCongr (Metric.closedBall (0 : btE) 1 \ {0}) btOmega := by
  obtain ⟨t, ht⟩ := btGoodAngle
  have hset : (Metric.closedBall (0 : btE) 1 \ {0}) \
      (btBad ∩ Metric.closedBall (0 : btE) 1) = btOmega := by
    simp only [btOmega]
    ext x
    simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_union,
      Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨hB, h0⟩, hC⟩
      refine ⟨hB, fun h => ?_⟩
      rcases h with h00 | hBad
      · exact h0 h00
      · exact hC ⟨hBad, hB⟩
    · rintro ⟨hB, h⟩
      refine ⟨⟨hB, fun e => h (Or.inl e)⟩, fun hC => h ?_⟩
      obtain ⟨hBad, -⟩ := hC
      exact Or.inr hBad
  have hY : ∀ n : ℕ, (btIsoOfUnitary (btRotY t))^[n] ''
      (btBad ∩ Metric.closedBall (0 : btE) 1) ⊆
      Metric.closedBall (0 : btE) 1 \ {0} := by
    intro n y hy
    obtain ⟨z, hzC, rfl⟩ := hy
    obtain ⟨hzBad, hzB⟩ := hzC
    simp only [btBad, Set.mem_ofPred_eq] at hzBad
    obtain ⟨hz0, -, -, -⟩ := hzBad
    have hnorm : ‖(btIsoOfUnitary (btRotY t))^[n] z‖ = ‖z‖ := by
      rw [btRotY_iterate t n z]
      exact btIsoOfUnitary_norm _ _
    have hzB' := Metric.mem_closedBall.mp hzB
    rw [dist_zero_right] at hzB'
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, hnorm]
      exact hzB'
    · intro hcon
      apply hz0
      have hz00 : z = 0 := norm_eq_zero.mp (by rw [← hnorm, hcon, norm_zero])
      exact hz00
  have hdisj : ∀ n : ℕ, 1 ≤ n → Disjoint
      ((btIsoOfUnitary (btRotY t))^[n] ''
        (btBad ∩ Metric.closedBall (0 : btE) 1))
      (btBad ∩ Metric.closedBall (0 : btE) 1) := by
    intro n hn
    rw [Set.disjoint_left]
    rintro a ⟨z, hzC, rfl⟩ haC
    obtain ⟨hzBad, -⟩ := hzC
    obtain ⟨haBad, -⟩ := haC
    simp only [btBad, Set.mem_ofPred_eq] at hzBad haBad
    obtain ⟨hz0, w, hw, hwfix⟩ := hzBad
    obtain ⟨-, v, hv, hvfix⟩ := haBad
    obtain ⟨s, hs⟩ := btU_fix w hw z hwfix
    obtain ⟨s', hs'⟩ := btU_fix v hv _ hvfix
    have hs0 : s ≠ 0 := by
      intro h0
      apply hz0
      have hz00 : WithLp.ofLp z = 0 := by rw [hs, h0, zero_smul]
      apply WithLp.ofLp_injective
      exact hz00.trans btOfLp_zero.symm
    have hcoord : WithLp.ofLp ((btIsoOfUnitary (btRotY t))^[n] z) =
        Matrix.mulVec (btRotY (↑n * t) : Matrix (Fin 3) (Fin 3) ℝ)
          (WithLp.ofLp z) := by
      rw [btRotY_iterate t n z]
      exact btIsoOfUnitary_apply _ _
    have heq : s • Matrix.mulVec (btRotY (↑n * t) : Matrix (Fin 3) (Fin 3) ℝ)
        (btU w) = s' • btU v := by
      rw [hs] at hcoord
      rw [Matrix.mulVec_smul] at hcoord
      rw [hs'] at hcoord
      exact hcoord.symm
    have hMw : dotProduct
        (Matrix.mulVec (btRotY (↑n * t) : Matrix (Fin 3) (Fin 3) ℝ) (btU w))
        (Matrix.mulVec (btRotY (↑n * t) : Matrix (Fin 3) (Fin 3) ℝ) (btU w)) =
        1 := by
      rw [btRotY_dot, btU_dot w hw]
    have hss : s * s = s' * s' := by
      have e1 : dotProduct
          (s • Matrix.mulVec (btRotY (↑n * t) : Matrix (Fin 3) (Fin 3) ℝ) (btU w))
          (s • Matrix.mulVec (btRotY (↑n * t) : Matrix (Fin 3) (Fin 3) ℝ) (btU w)) =
          dotProduct (s' • btU v) (s' • btU v) := by rw [heq]
      simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, hMw,
        btU_dot v hv, mul_one] at e1
      exact e1
    have hs0' : s' ≠ 0 := by
      intro h0
      have h := mul_ne_zero hs0 hs0
      rw [hss, h0, mul_zero] at h
      exact h rfl
    have hεsq : (s' / s) * (s' / s) = 1 := by
      rw [div_mul_div_comm, hss]
      exact div_self (mul_ne_zero hs0' hs0')
    have hε12 : s' / s = 1 ∨ s' / s = -1 :=
      (mul_self_eq_mul_self_iff (a := s' / s) (b := 1)).mp
        (by rw [hεsq, mul_one])
    have hfin : Matrix.mulVec (btRotY (↑n * t) : Matrix (Fin 3) (Fin 3) ℝ)
        (btU w) = (s' / s) • btU v := by
      have e := congrArg ((s⁻¹) • ·) heq
      rw [← mul_smul, ← mul_smul, inv_mul_cancel₀ hs0, one_smul] at e
      have hss' : s⁻¹ * s' = s' / s := by rw [div_eq_mul_inv]; ring
      rw [← hss']
      exact e
    exact ht w v hw hv n hn (s' / s) hε12 hfin
  have h := btCongr_absorb (btIsoOfUnitary (btRotY t)) hY hdisj
  rw [hset] at h
  exact h

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted
