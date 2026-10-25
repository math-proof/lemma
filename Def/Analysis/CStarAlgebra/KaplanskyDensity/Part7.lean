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
import Theorem.Analysis.CStarAlgebra.KaplanskyDensity.Part6
open scoped PointwiseConvergenceCLM
open Topology


namespace Analysis.CStarAlgebra.KaplanskyDensityWanted

universe u

section KapCorner

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The 2x2 corner algebra on `H ⊕ H`: operators whose four corners lie in `S`. -/
noncomputable def kapCorner (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    StarSubalgebra ℂ (WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H)) where
  carrier := {T | kapFst ∘L T ∘L kapInl ∈ S ∧ kapFst ∘L T ∘L kapInr ∈ S ∧
    kapSnd ∘L T ∘L kapInl ∈ S ∧ kapSnd ∘L T ∘L kapInr ∈ S}
  zero_mem' := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      (rw [kapCorner_zero_eq]; exact zero_mem S)
  add_mem' := by
    intro T U hT hU
    obtain ⟨hT11, hT12, hT21, hT22⟩ := hT
    obtain ⟨hU11, hU12, hU21, hU22⟩ := hU
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [kapCorner_add_eq]; exact add_mem hT11 hU11
    · rw [kapCorner_add_eq]; exact add_mem hT12 hU12
    · rw [kapCorner_add_eq]; exact add_mem hT21 hU21
    · rw [kapCorner_add_eq]; exact add_mem hT22 hU22
  mul_mem' := by
    intro T U hT hU
    obtain ⟨hT11, hT12, hT21, hT22⟩ := hT
    obtain ⟨hU11, hU12, hU21, hU22⟩ := hU
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [kapCorner_mul_eq]; exact add_mem (mul_mem hT11 hU11) (mul_mem hT12 hU21)
    · rw [kapCorner_mul_eq]; exact add_mem (mul_mem hT11 hU12) (mul_mem hT12 hU22)
    · rw [kapCorner_mul_eq]; exact add_mem (mul_mem hT21 hU11) (mul_mem hT22 hU21)
    · rw [kapCorner_mul_eq]; exact add_mem (mul_mem hT21 hU12) (mul_mem hT22 hU22)
  algebraMap_mem' := by
    intro c
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [kapCorner_alg_11]; exact S.algebraMap_mem c
    · rw [kapCorner_alg_12]; exact zero_mem S
    · rw [kapCorner_alg_21]; exact zero_mem S
    · rw [kapCorner_alg_22]; exact S.algebraMap_mem c
  star_mem' := by
    intro T hT
    obtain ⟨hT11, hT12, hT21, hT22⟩ := hT
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [kapCorner_star_11]; exact star_mem hT11
    · rw [kapCorner_star_12]; exact star_mem hT21
    · rw [kapCorner_star_21]; exact star_mem hT12
    · rw [kapCorner_star_22]; exact star_mem hT22

end KapCorner
end Analysis.CStarAlgebra.KaplanskyDensityWanted
