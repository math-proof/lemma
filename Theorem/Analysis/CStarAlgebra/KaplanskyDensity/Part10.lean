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
import Def.Analysis.CStarAlgebra.KaplanskyDensity.Part10
open scoped PointwiseConvergenceCLM
open Topology


namespace Analysis.CStarAlgebra.KaplanskyDensityWanted

universe u

section KapGamma

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The corner map is SOT-continuous. -/
theorem kapGamma_continuous :
    Continuous (fun P : WithLp 2 (H × H) →Lₚₜ[ℂ] WithLp 2 (H × H) => kapGamma P) := by
  refine PointwiseConvergenceCLM.continuous_of_continuous_eval fun w => ?_
  have key : ∀ P : WithLp 2 (H × H) →Lₚₜ[ℂ] WithLp 2 (H × H),
      kapGamma P w = kapFst (P (kapInr w)) := by
    intro P
    unfold kapGamma
    simp only [kapOfBounded_apply, ContinuousLinearMap.comp_apply,
      kapToBounded_apply]
  simp only [key]
  exact kapFst.cont.comp (kapEval_continuous (kapInr w))

omit [CompleteSpace H] in
/-- The corner map does not increase the norm. -/
theorem kapGamma_norm (T : WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H))
    (hT : ‖T‖ ≤ 1) : ‖kapFst ∘L T ∘L kapInr‖ ≤ 1 := by
  have hF : ∀ w : WithLp 2 (H × H), ‖kapFst w‖ ≤ ‖w‖ := by
    intro w
    calc ‖kapFst w‖ ≤ ‖(kapFst : WithLp 2 (H × H) →L[ℂ] H)‖ * ‖w‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖w‖ :=
        mul_le_mul_of_nonneg_right kapNorm_fst_le (norm_nonneg w)
      _ = ‖w‖ := one_mul _
  have hT' : ∀ u : WithLp 2 (H × H), ‖T u‖ ≤ ‖u‖ := by
    intro u
    calc ‖T u‖ ≤ ‖T‖ * ‖u‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right hT (norm_nonneg u)
      _ = ‖u‖ := one_mul _
  have hI : ∀ v : H, ‖kapInr v‖ ≤ ‖v‖ := by
    intro v
    calc ‖kapInr v‖ ≤ ‖(kapInr : H →L[ℂ] WithLp 2 (H × H))‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right kapNorm_inr_le (norm_nonneg v)
      _ = ‖v‖ := one_mul _
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => ?_)
  rw [one_mul]
  calc ‖(kapFst ∘L T ∘L kapInr) v‖ = ‖kapFst (T (kapInr v))‖ := rfl
    _ ≤ ‖T (kapInr v)‖ := hF _
    _ ≤ ‖kapInr v‖ := hT' _
    _ ≤ ‖v‖ := hI _

/-- The corner map sends the corner ball into the ball of `S`. -/
theorem kapGamma_maps (S : StarSubalgebra ℂ (H →L[ℂ] H))
    {P : WithLp 2 (H × H) →Lₚₜ[ℂ] WithLp 2 (H × H)}
    (hP : P ∈ {P : WithLp 2 (H × H) →Lₚₜ[ℂ] WithLp 2 (H × H) |
        toBounded P ∈ ↑(kapCorner S)} ∩
      {P : WithLp 2 (H × H) →Lₚₜ[ℂ] WithLp 2 (H × H) | ‖toBounded P‖ ≤ 1}) :
    kapGamma P ∈ {p : H →Lₚₜ[ℂ] H | toBounded p ∈ (↑S : Set (H →L[ℂ] H))} ∩
      {p : H →Lₚₜ[ℂ] H | ‖toBounded p‖ ≤ 1} := by
  obtain ⟨hPcorner, hPnorm⟩ := hP
  have hcorn : toBounded (kapGamma P) = kapFst ∘L toBounded P ∘L kapInr :=
    kapToBounded_ofBounded _
  have h12 : kapFst ∘L toBounded P ∘L kapInr ∈ (↑S : Set (H →L[ℂ] H)) :=
    ((kapMem_corner S _).mp hPcorner).2.1
  have hmem : toBounded (kapGamma P) ∈ (↑S : Set (H →L[ℂ] H)) := by
    rw [hcorn]; exact h12
  have hnorm : ‖toBounded (kapGamma P)‖ ≤ 1 := by
    rw [hcorn]; exact kapGamma_norm _ hPnorm
  exact ⟨hmem, hnorm⟩

end KapGamma

/--
For a complex Hilbert space `H` and unital `∗`-subalgebra `S ⊆ B(H)`, the SOT-closure of its
operator-norm unit ball equals the unit ball of its SOT-closure, with norm and membership read via
`toBounded` and closure taken in `H →Lₚₜ[ℂ] H`. Source: Kaplansky density theorem, I. Kaplansky,
Pacific J. Math. 1 (1951), 227–232; see Takesaki, Theory of Operator Algebras I, Density Theorem
and Kadison–Ringrose Vol I; Lean is SOT-closure equality of unit balls via toBounded conversion,
full infinite-dimensional form.

Proves `Wanted` entry `kaplansky_density_theorem`.
-/
theorem kaplansky_density_theorem
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure ({x : H →Lₚₜ[ℂ] H | toBounded x ∈ (S : Set (H →L[ℂ] H)) ∧ ‖toBounded x‖ ≤ 1} :
      Set (H →Lₚₜ[ℂ] H))
    = {y : H →Lₚₜ[ℂ] H | y ∈ closure ({p : H →Lₚₜ[ℂ] H | toBounded p ∈ (S : Set (H →L[ℂ] H))} :
      Set (H →Lₚₜ[ℂ] H)) ∧ ‖toBounded y‖ ≤ 1} := by
  have hset : ({x : H →Lₚₜ[ℂ] H | toBounded x ∈ (S : Set (H →L[ℂ] H)) ∧
      ‖toBounded x‖ ≤ 1} : Set (H →Lₚₜ[ℂ] H))
      = {p : H →Lₚₜ[ℂ] H | toBounded p ∈ (↑S : Set (H →L[ℂ] H))} ∩
        {p : H →Lₚₜ[ℂ] H | ‖toBounded p‖ ≤ 1} := rfl
  rw [hset]
  apply Set.ext
  intro z
  constructor
  · intro hz
    constructor
    · exact closure_mono Set.inter_subset_left hz
    · exact closure_minimal Set.inter_subset_right kapIsClosed_ball hz
  · intro hz
    obtain ⟨hymem, hnorm⟩ := hz
    have hxmem : kapOfBounded (toBounded z)
        ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ (↑S : Set (H →L[ℂ] H))} := by
      rw [kapOfBounded_toBounded]
      exact hymem
    have hXsa : IsSelfAdjoint (kapOffDiag (toBounded z)) :=
      kapOffDiag_selfAdjoint _
    have hXnorm : ‖kapOffDiag (toBounded z)‖ ≤ 1 :=
      kapOffDiag_norm _ hnorm
    have hXmem : kapOfBounded (kapOffDiag (toBounded z)) ∈ closure
        {P : WithLp 2 (H × H) →Lₚₜ[ℂ] WithLp 2 (H × H) |
          toBounded P ∈ ↑(kapCorner S)} :=
      kapOffDiag_mem_closure S _ hxmem
    have hball := kapSelfAdjoint_mem_closure_ball (kapCorner S)
      (kapOffDiag (toBounded z)) hXsa hXnorm hXmem
    have hmaps : Set.MapsTo
        (fun P : WithLp 2 (H × H) →Lₚₜ[ℂ] WithLp 2 (H × H) => kapGamma P)
        ({P : WithLp 2 (H × H) →Lₚₜ[ℂ] WithLp 2 (H × H) |
            toBounded P ∈ ↑(kapCorner S)} ∩
          {P : WithLp 2 (H × H) →Lₚₜ[ℂ] WithLp 2 (H × H) | ‖toBounded P‖ ≤ 1})
        ({p : H →Lₚₜ[ℂ] H | toBounded p ∈ (↑S : Set (H →L[ℂ] H))} ∩
          {p : H →Lₚₜ[ℂ] H | ‖toBounded p‖ ≤ 1}) := by
      intro P hP
      exact kapGamma_maps S hP
    have hfin := map_mem_closure kapGamma_continuous hball hmaps
    have hfin' : kapGamma (kapOfBounded (kapOffDiag (toBounded z))) ∈ closure
        ({p : H →Lₚₜ[ℂ] H | toBounded p ∈ (↑S : Set (H →L[ℂ] H))} ∩
          {p : H →Lₚₜ[ℂ] H | ‖toBounded p‖ ≤ 1}) := hfin
    have heq : kapGamma (kapOfBounded (kapOffDiag (toBounded z))) = z := by
      have h1 : kapGamma (kapOfBounded (kapOffDiag (toBounded z)))
          = kapOfBounded (kapFst ∘L kapOffDiag (toBounded z) ∘L kapInr) := by
        unfold kapGamma
        rw [kapToBounded_ofBounded]
      rw [h1, kapOffDiag_corner, kapOfBounded_toBounded]
    rw [heq] at hfin'
    exact hfin'

end Analysis.CStarAlgebra.KaplanskyDensityWanted
