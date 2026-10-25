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
import Def.Analysis.CStarAlgebra.KaplanskyDensity.Part9
open scoped PointwiseConvergenceCLM
open Topology


namespace Analysis.CStarAlgebra.KaplanskyDensityWanted

universe u

section KapPsi

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The pair-to-corner map is SOT-continuous. -/
theorem kapPsi_continuous :
    Continuous (fun pq : (H →Lₚₜ[ℂ] H) × (H →Lₚₜ[ℂ] H) => kapPsi pq.1 pq.2) := by
  refine PointwiseConvergenceCLM.continuous_of_continuous_eval fun w => ?_
  have key : ∀ pq : (H →Lₚₜ[ℂ] H) × (H →Lₚₜ[ℂ] H), kapPsi pq.1 pq.2 w
      = kapInl (pq.1 (kapSnd w)) + kapInr (pq.2 (kapFst w)) := by
    intro pq
    unfold kapPsi
    simp only [kapOfBounded_apply, add_apply, ContinuousLinearMap.comp_apply,
      kapToBounded_apply]
  simp only [key]
  exact (kapInl.cont.comp ((kapEval_continuous _).comp continuous_fst)).add
    (kapInr.cont.comp ((kapEval_continuous _).comp continuous_snd))

/-- The four corners of `Ψ p q` are `0`, `toBounded p`, `toBounded q`, `0`. -/
theorem kapPsi_corners (p q : H →Lₚₜ[ℂ] H) :
    kapFst ∘L toBounded (kapPsi p q) ∘L kapInl = 0 ∧
    kapFst ∘L toBounded (kapPsi p q) ∘L kapInr = toBounded p ∧
    kapSnd ∘L toBounded (kapPsi p q) ∘L kapInl = toBounded q ∧
    kapSnd ∘L toBounded (kapPsi p q) ∘L kapInr = 0 := by
  have hT : toBounded (kapPsi p q)
      = kapInl ∘L toBounded p ∘L kapSnd + kapInr ∘L toBounded q ∘L kapFst :=
    kapToBounded_ofBounded _
  rw [hT]
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext v
    simp only [ContinuousLinearMap.comp_apply, add_apply, map_add, map_zero,
      kapSnd_kapInl_apply, kapFst_kapInl_apply, kapFst_kapInr_apply, add_zero,
      zero_apply]
  · ext v
    simp only [ContinuousLinearMap.comp_apply, add_apply, map_zero,
      kapSnd_kapInr_apply, kapFst_kapInr_apply, kapFst_kapInl_apply, add_zero]
  · ext v
    simp only [ContinuousLinearMap.comp_apply, add_apply, map_zero,
      kapSnd_kapInl_apply, kapFst_kapInl_apply, kapSnd_kapInr_apply, zero_add]
  · ext v
    simp only [ContinuousLinearMap.comp_apply, add_apply, map_add, map_zero,
      kapSnd_kapInr_apply, kapFst_kapInr_apply, kapSnd_kapInl_apply, zero_add,
      zero_apply]

/-- `Ψ` maps `Ŝ ×ˢ Ŝ` into the corner preimage set. -/
theorem kapPsi_mem_corner (S : StarSubalgebra ℂ (H →L[ℂ] H))
    {p q : H →Lₚₜ[ℂ] H} (hp : toBounded p ∈ (↑S : Set (H →L[ℂ] H)))
    (hq : toBounded q ∈ (↑S : Set (H →L[ℂ] H))) :
    kapPsi p q ∈ {P : WithLp 2 (H × H) →Lₚₜ[ℂ] WithLp 2 (H × H) |
      toBounded P ∈ ↑(kapCorner S)} := by
  obtain ⟨e11, e12, e21, e22⟩ := kapPsi_corners p q
  have h11 : kapFst ∘L toBounded (kapPsi p q) ∘L kapInl ∈ (↑S : Set (H →L[ℂ] H)) := by
    rw [e11]; exact zero_mem S
  have h12 : kapFst ∘L toBounded (kapPsi p q) ∘L kapInr ∈ (↑S : Set (H →L[ℂ] H)) := by
    rw [e12]; exact hp
  have h21 : kapSnd ∘L toBounded (kapPsi p q) ∘L kapInl ∈ (↑S : Set (H →L[ℂ] H)) := by
    rw [e21]; exact hq
  have h22 : kapSnd ∘L toBounded (kapPsi p q) ∘L kapInr ∈ (↑S : Set (H →L[ℂ] H)) := by
    rw [e22]; exact zero_mem S
  exact ⟨h11, h12, h21, h22⟩

/-- The off-diagonal lift lies in the SOT-closure of the corner algebra. -/
theorem kapOffDiag_mem_closure (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : H →L[ℂ] H)
    (hxmem : kapOfBounded x
      ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ (↑S : Set (H →L[ℂ] H))}) :
    kapOfBounded (kapOffDiag x) ∈ closure
      {P : WithLp 2 (H × H) →Lₚₜ[ℂ] WithLp 2 (H × H) |
        toBounded P ∈ ↑(kapCorner S)} := by
  have hstar : kapStar (kapOfBounded x)
      ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ (↑S : Set (H →L[ℂ] H))} :=
    kapStar_mem_closure_of_convex (kapSotConvex S) (kapSotStar S) hxmem
  have hpair : (kapOfBounded x, kapStar (kapOfBounded x)) ∈ closure
      ({p : H →Lₚₜ[ℂ] H | toBounded p ∈ (↑S : Set (H →L[ℂ] H))} ×ˢ
        {p : H →Lₚₜ[ℂ] H | toBounded p ∈ (↑S : Set (H →L[ℂ] H))}) := by
    rw [closure_prod_eq]
    exact ⟨hxmem, hstar⟩
  have hmaps : Set.MapsTo
      (fun pq : (H →Lₚₜ[ℂ] H) × (H →Lₚₜ[ℂ] H) => kapPsi pq.1 pq.2)
      ({p : H →Lₚₜ[ℂ] H | toBounded p ∈ (↑S : Set (H →L[ℂ] H))} ×ˢ
        {p : H →Lₚₜ[ℂ] H | toBounded p ∈ (↑S : Set (H →L[ℂ] H))})
      {P : WithLp 2 (H × H) →Lₚₜ[ℂ] WithLp 2 (H × H) |
        toBounded P ∈ ↑(kapCorner S)} := by
    intro pq hpq
    obtain ⟨hp1, hp2⟩ := hpq
    exact kapPsi_mem_corner S hp1 hp2
  have hmap := map_mem_closure kapPsi_continuous hpair hmaps
  have hmap' : kapPsi (kapOfBounded x) (kapStar (kapOfBounded x)) ∈ closure
      {P : WithLp 2 (H × H) →Lₚₜ[ℂ] WithLp 2 (H × H) |
        toBounded P ∈ ↑(kapCorner S)} := hmap
  have heq : kapPsi (kapOfBounded x) (kapStar (kapOfBounded x))
      = kapOfBounded (kapOffDiag x) := by
    unfold kapPsi kapOffDiag
    rw [kapToBounded_star, kapToBounded_ofBounded]
  rw [heq] at hmap'
  exact hmap'

end KapPsi
end Analysis.CStarAlgebra.KaplanskyDensityWanted
