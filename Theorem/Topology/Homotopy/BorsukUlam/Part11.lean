/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.BallSphere
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.UniformSpace.HeineCantor
import Def.Topology.Homotopy.BorsukUlam.Part14


namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

/-- An odd map on the cube has a zero in the unit ball. -/
theorem bu_no_zero {n : ℕ} [Nonempty (Fin n)]
    {g : (Fin n → ℝ) → (Fin n → ℝ)} (hg : Continuous g)
    (hodd : ∀ x : Fin n → ℝ, ‖x‖ = 1 → g (-x) = -g x) :
    ∃ x ∈ Metric.closedBall (0 : Fin n → ℝ) 1, g x = 0 := by
  by_contra hcon
  have hne : ∀ x ∈ Metric.closedBall (0 : Fin n → ℝ) 1, g x ≠ 0 := by
    intro x hx heq
    exact hcon ⟨x, hx, heq⟩
  obtain ⟨ε, hεpos, hε, δ, hδpos, hδε⟩ := bu_eps_delta hg hne
  obtain ⟨m, hmgt⟩ := exists_nat_gt (1 / δ)
  have hδnn : (0 : ℝ) < 1 / δ := one_div_pos.mpr hδpos
  have hm0 : 0 < m := by
    have hR : (0 : ℝ) < (m : ℝ) := lt_trans hδnn hmgt
    exact_mod_cast hR
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have h1m : (1 : ℝ) / (m : ℝ) < δ := by
    have h := one_div_lt_one_div_of_lt hδnn hmgt
    rwa [one_div_one_div] at h
  have hbox : ∀ z ∈ bu_tkBox n m, buPt m z ∈ Metric.closedBall (0 : Fin n → ℝ) 1 :=
    fun z hz => buPt_mem hmR hz
  have hnorm1 : ∀ z ∈ bu_tkBox n m, (∃ i, |z i| = (m : ℤ)) → ‖buPt m z‖ = 1 :=
    fun z hz hbd => buPt_norm_one hmR hz hbd
  have hPtneg : ∀ z : Fin n → ℤ, buPt m (-z) = -buPt m z := fun z => buPt_neg z
  have hanti : ∀ z ∈ bu_tkBox n m, (∃ i, |z i| = (m : ℤ)) →
      (fun z => buLab (g (buPt m z))) (-z) =
        bu_tkNeg ((fun z => buLab (g (buPt m z))) z) := by
    intro z hz hbd
    change buLab (g (buPt m (-z))) = bu_tkNeg (buLab (g (buPt m z)))
    have h1 : g (buPt m (-z)) = -g (buPt m z) := by
      rw [hPtneg]
      exact hodd _ (hnorm1 z hz hbd)
    rw [h1]
    exact buLab_neg (hne _ (hbox z hz))
  obtain ⟨z, hz, w, hw, hle, heq⟩ :=
    bu_tucker (L := fun z => buLab (g (buPt m z))) hm0 hanti
  have heq_fst : decide (0 < (g (buPt m w)) (buI (g (buPt m w)))) =
      !(decide (0 < (g (buPt m z)) (buI (g (buPt m z))))) :=
    congrArg Prod.fst heq
  have heq_snd : buI (g (buPt m w)) = buI (g (buPt m z)) := congrArg Prod.snd heq
  rw [heq_snd] at heq_fst
  have haI : (g (buPt m z)) (buI (g (buPt m z))) ≠ 0 :=
    buI_ne_zero_of_ne (hne _ (hbox z hz))
  have hbI : (g (buPt m w)) (buI (g (buPt m z))) ≠ 0 := by
    rw [← heq_snd]
    exact buI_ne_zero_of_ne (hne _ (hbox w hw))
  have hsign : (0 < (g (buPt m z)) (buI (g (buPt m z))) ∧
        (g (buPt m w)) (buI (g (buPt m z))) < 0) ∨
      ((g (buPt m z)) (buI (g (buPt m z))) < 0 ∧
        0 < (g (buPt m w)) (buI (g (buPt m z)))) := by
    by_cases hda : 0 < (g (buPt m z)) (buI (g (buPt m z)))
    · left
      refine ⟨hda, ?_⟩
      have hdb : decide (0 < (g (buPt m w)) (buI (g (buPt m z)))) = false := by
        rw [heq_fst, decide_eq_true hda, Bool.not_true]
      have hn : ¬ 0 < (g (buPt m w)) (buI (g (buPt m z))) := of_decide_eq_false hdb
      exact lt_of_le_of_ne (not_lt.mp hn) (fun he => hbI he)
    · right
      have halt : (g (buPt m z)) (buI (g (buPt m z))) < 0 :=
        lt_of_le_of_ne (not_lt.mp hda) (fun he => haI he)
      have hdb : decide (0 < (g (buPt m w)) (buI (g (buPt m z)))) = true := by
        rw [heq_fst, decide_eq_false hda, Bool.not_false]
      exact ⟨halt, of_decide_eq_true hdb⟩
  have hgap : |(g (buPt m z)) (buI (g (buPt m z)))| ≤
      |(g (buPt m z)) (buI (g (buPt m z))) - (g (buPt m w)) (buI (g (buPt m z)))| := by
    rcases hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hle1 : (g (buPt m z)) (buI (g (buPt m z))) ≤
          (g (buPt m z)) (buI (g (buPt m z))) - (g (buPt m w)) (buI (g (buPt m z))) := by
        linarith
      rw [abs_of_pos h1]
      exact le_trans hle1 (le_abs_self _)
    · have hle1 : (g (buPt m z)) (buI (g (buPt m z))) -
          (g (buPt m w)) (buI (g (buPt m z))) ≤
          (g (buPt m z)) (buI (g (buPt m z))) := by
        linarith
      have hneg : (g (buPt m z)) (buI (g (buPt m z))) -
          (g (buPt m w)) (buI (g (buPt m z))) < 0 :=
        lt_of_le_of_lt hle1 h1
      rw [abs_of_neg h1, abs_of_neg hneg]
      linarith
  have hclose : dist (g (buPt m z)) (g (buPt m w)) < ε :=
    hδε _ (hbox z hz) _ (hbox w hw) (buPt_dist hmR hle |>.trans_lt h1m)
  have hfar : ε ≤ dist (g (buPt m z)) (g (buPt m w)) := by
    rw [dist_eq_norm]
    have h1 : |(g (buPt m z)) (buI (g (buPt m z))) -
        (g (buPt m w)) (buI (g (buPt m z)))| ≤ ‖g (buPt m z) - g (buPt m w)‖ := by
      have h2 := norm_le_pi_norm (g (buPt m z) - g (buPt m w)) (buI (g (buPt m z)))
      rwa [Real.norm_eq_abs, Pi.sub_apply] at h2
    have h3 : ‖g (buPt m z)‖ ≤ ‖g (buPt m z) - g (buPt m w)‖ := by
      rw [buI_norm (g (buPt m z))]
      exact le_trans hgap h1
    exact le_trans (hε _ (hbox z hz)) h3
  linarith

/--
Every continuous `S^n → ℝ^n` identifies an antipodal pair `∃ x, f x = f (-x)`. Source: K. Borsuk,
Fund. Math. 20 (1933) 177–190 antipodal theorem; S. Ulam; J. Matoušek, Using the Borsuk–Ulam
Theorem; Lean states `EuclideanSpace ℝ (Fin (n+1))` to `Fin n` specialization.

Proves `Wanted` entry `borsukUlam`.
-/
theorem borsukUlam
    {n : ℕ} (f : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → EuclideanSpace ℝ (Fin n))
    (hf : Continuous f) :
    ∃ x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, f x = f (-x) := by
  cases n with
  | zero =>
    refine ⟨buLift 0 0, ?_⟩
    apply PiLp.ext
    intro i
    exact Fin.elim0 i
  | succ k =>
    have hg : Continuous (buG (k + 1) f) := buG_continuous hf
    have hodd : ∀ x : Fin (k + 1) → ℝ, ‖x‖ = 1 → buG (k + 1) f (-x) = -buG (k + 1) f x :=
      fun x hx => buG_neg_of_norm_one hx
    obtain ⟨x, _, hx0⟩ := bu_no_zero hg hodd
    exact ⟨buLift (k + 1) x, buG_zero hx0⟩

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
