/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Analysis.LocallyConvex.PointwiseConvergence
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Def.Analysis.CStarAlgebra.KaplanskyDensity.Part5
open scoped PointwiseConvergenceCLM
open Topology


namespace Analysis.CStarAlgebra.KaplanskyDensityWanted

universe u

section KapCayleyInverse

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem kapG_cont : Continuous kapG := by
  unfold kapG
  refine Continuous.div continuous_id
    (continuous_const.add
      (Real.continuous_sqrt.comp
        (by continuity : Continuous (fun t : ℝ => 1 - t ^ 2)))) (fun t => ?_)
  have hnn : (0 : ℝ) ≤ Real.sqrt (1 - t ^ 2) := Real.sqrt_nonneg _
  have hpos : (0 : ℝ) < 1 + Real.sqrt (1 - t ^ 2) := by linarith
  exact ne_of_gt hpos

/-- The inverse Cayley cfc inverts `kapCfcF` on the unit ball. -/
theorem kapCfcF_cfcG (x : H →L[ℂ] H) (hx : IsSelfAdjoint x)
    (hnorm : ‖x‖ ≤ 1) :
    kapCfcF (cfc kapG x) = x := by
  have hspec : ∀ t ∈ spectrum ℝ x, |t| ≤ 1 := by
    have h := (norm_cfc_le_iff (id : ℝ → ℝ) x zero_le_one
      (hf := continuous_id.continuousOn) (ha := hx)).mp ?_
    · intro t ht
      have ht1 := h t ht
      simpa [Real.norm_eq_abs] using ht1
    · have hid : cfc (id : ℝ → ℝ) x = x := cfc_id (R := ℝ) (a := x) (ha := hx)
      rwa [hid]
  have hscalar : ∀ t ∈ spectrum ℝ x, (kapF ∘ kapG) t = id t := by
    intro t ht
    have habs : |t| ≤ 1 := hspec t ht
    have hnn : (0 : ℝ) ≤ 1 - t ^ 2 := by
      have h2 : |t| ^ 2 ≤ 1 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr habs) (abs_nonneg t)]
      rw [sq_abs] at h2
      linarith
    have hsnn : (0 : ℝ) ≤ Real.sqrt (1 - t ^ 2) := Real.sqrt_nonneg _
    have hs2 : (Real.sqrt (1 - t ^ 2)) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt hnn
    have hspos : (0 : ℝ) < 1 + Real.sqrt (1 - t ^ 2) := by linarith
    have hne : (1 : ℝ) + Real.sqrt (1 - t ^ 2) ≠ 0 := ne_of_gt hspos
    set s : ℝ := Real.sqrt (1 - t ^ 2) with hsdef
    have hden : 1 + (t / (1 + s)) ^ 2 = 2 / (1 + s) := by
      have e1 : (t / (1 + s)) ^ 2 = t ^ 2 / ((1 + s) * (1 + s)) := by
        simp only [pow_two, div_mul_div_comm]
      have e3 : ((1 + s) ^ 2 + t ^ 2) = 2 * (1 + s) := by
        linear_combination hs2
      have e4 : (1 : ℝ) + t ^ 2 / ((1 + s) * (1 + s))
          = ((1 + s) ^ 2 + t ^ 2) / ((1 + s) * (1 + s)) := by
        have hD : ((1 + s) * (1 + s)) ≠ 0 := mul_ne_zero hne hne
        field_simp
      rw [e1, e4, e3, div_eq_div_iff (mul_ne_zero hne hne) hne]
      ring
    change kapF (kapG t) = t
    unfold kapG kapF
    rw [hden, div_eq_iff (ne_of_gt (div_pos (by norm_num) hspos)),
      ← mul_div_assoc, ← mul_div_assoc, mul_comm (2 : ℝ) t]
  have hfin : cfc (kapF ∘ kapG) x = cfc id x := cfc_congr' hscalar
  have hcomp := cfc_comp (g := kapF) (f := kapG) (a := x) (ha := hx)
    (hg := kapF_cont.continuousOn) (hf := kapG_cont.continuousOn)
  have hid : cfc (id : ℝ → ℝ) x = x := cfc_id (R := ℝ) (a := x) (ha := hx)
  unfold kapCfcF
  rw [← hcomp, hfin, hid]

/-- The inverse Cayley cfc of a self-adjoint element is self-adjoint. -/
theorem kapIsSelfAdjoint_cfcG (x : H →L[ℂ] H) :
    IsSelfAdjoint (cfc kapG x) :=
  IsSelfAdjoint.cfc

end KapCayleyInverse

section KapSelfAdjoint

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Self-adjoint Kaplansky density: a self-adjoint norm-one element of the SOT-closure
    of `S` is an SOT-limit of the unit ball of `S`. -/
theorem kapSelfAdjoint_mem_closure_ball (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : H →L[ℂ] H) (hx : IsSelfAdjoint x) (hnorm : ‖x‖ ≤ 1)
    (hxmem : kapOfBounded x
      ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}) :
    kapOfBounded x ∈ closure ({p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S} ∩
      {p : H →Lₚₜ[ℂ] H | ‖toBounded p‖ ≤ 1}) := by
  have hxS : x ∈ kapSotClosure S := (kapMem_sotClosure S x).mpr hxmem
  have hclosed : IsClosed (↑(kapSotClosure S) : Set (H →L[ℂ] H)) :=
    kapIsClosed_sotClosure S
  have hyS : cfc kapG x ∈ kapSotClosure S := cfc_mem kapG hxS
  have hymem : kapOfBounded (cfc kapG x)
      ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S} :=
    (kapMem_sotClosure S _).mp hyS
  have hysa : IsSelfAdjoint (cfc kapG x) := kapIsSelfAdjoint_cfcG x
  have hyfix : kapStar (kapOfBounded (cfc kapG x))
      = kapOfBounded (cfc kapG x) := by
    rw [kapStar_eq_iff, kapToBounded_ofBounded]
    exact hysa
  have hysa_mem : kapOfBounded (cfc kapG x)
      ∈ closure {p : H →Lₚₜ[ℂ] H | p ∈ {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}
        ∧ kapStar p = p} :=
    kapMem_closure_fixed_of_convex (kapSotConvex S) (kapSotStar S) hymem hyfix
  have hsub : {p : H →Lₚₜ[ℂ] H | p ∈ {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}
        ∧ kapStar p = p}
      ⊆ {p : H →Lₚₜ[ℂ] H | IsSelfAdjoint (toBounded p)} := by
    intro p hp
    obtain ⟨-, hfix⟩ := hp
    exact (kapStar_eq_iff p).mp hfix
  have hne : (𝓝[{p : H →Lₚₜ[ℂ] H | p ∈ {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}
        ∧ kapStar p = p}] (kapOfBounded (cfc kapG x))).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp hysa_mem
  have : Filter.NeBot (𝓝[{p : H →Lₚₜ[ℂ] H | p ∈ {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}
        ∧ kapStar p = p}] (kapOfBounded (cfc kapG x))) := hne
  have htend0 := kapTendsto_cfcF (cfc kapG x) hysa
  have hmono : 𝓝[{p : H →Lₚₜ[ℂ] H | p ∈ {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}
          ∧ kapStar p = p}] (kapOfBounded (cfc kapG x))
        ≤ 𝓝[{p : H →Lₚₜ[ℂ] H | IsSelfAdjoint (toBounded p)}]
          (kapOfBounded (cfc kapG x)) :=
    nhdsWithin_mono _ hsub
  have htend := htend0.mono_left hmono
  have hlim : kapCfcF (cfc kapG x) = x := kapCfcF_cfcG x hx hnorm
  rw [hlim] at htend
  have hmaps : ∀ᶠ p in 𝓝[{p : H →Lₚₜ[ℂ] H | p ∈ {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}
          ∧ kapStar p = p}] (kapOfBounded (cfc kapG x)),
      kapOfBounded (kapCfcF (toBounded p))
        ∈ closure ({p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S} ∩
          {p : H →Lₚₜ[ℂ] H | ‖toBounded p‖ ≤ 1}) := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    obtain ⟨hpmem, hpfix⟩ := hp
    have hmemS : toBounded p ∈ (↑S : Set (H →L[ℂ] H)) := hpmem
    have hclosedS : IsClosed (↑(S.topologicalClosure) : Set (H →L[ℂ] H)) :=
      S.isClosed_topologicalClosure
    have hmemT : kapCfcF (toBounded p) ∈ S.topologicalClosure :=
      cfc_mem kapF (S.le_topologicalClosure hmemS)
    have hsa : IsSelfAdjoint (toBounded p) := by
      rw [← kapStar_eq_iff]
      exact hpfix
    have hnormF : ‖kapCfcF (toBounded p)‖ ≤ 1 := kapNorm_cfcF_le _
    exact kapOfBounded_mem_closure_ball _ hmemT hnormF
  exact isClosed_closure.mem_of_tendsto htend hmaps

end KapSelfAdjoint
end Analysis.CStarAlgebra.KaplanskyDensityWanted
