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
import Theorem.Analysis.CStarAlgebra.KaplanskyDensity.Part2
open scoped PointwiseConvergenceCLM
open Topology


namespace Analysis.CStarAlgebra.KaplanskyDensityWanted

universe u

section KapClosure

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The SOT-closure of `S`, read back as a star subalgebra of `B(H)`. -/
noncomputable def kapSotClosure (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    StarSubalgebra ℂ (H →L[ℂ] H) where
  carrier := {T | kapOfBounded T ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}}
  zero_mem' := by
    change kapOfBounded (0 : H →L[ℂ] H) ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}
    rw [kapOfBounded_zero]
    apply subset_closure
    change toBounded (0 : H →Lₚₜ[ℂ] H) ∈ ↑S
    rw [kapToBounded_zero]
    exact zero_mem S
  add_mem' := by
    intro T U hT hU
    have hT' : kapOfBounded T ∈ Submodule.topologicalClosure (kapSotSub S) := by
      rw [← SetLike.mem_coe, kapTopClosure_coe]
      exact hT
    have hU' : kapOfBounded U ∈ Submodule.topologicalClosure (kapSotSub S) := by
      rw [← SetLike.mem_coe, kapTopClosure_coe]
      exact hU
    change kapOfBounded (T + U) ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}
    rw [kapOfBounded_add, ← kapTopClosure_coe]
    exact add_mem hT' hU'
  mul_mem' := by
    intro T U hT hU
    have hT' : kapOfBounded T ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S} := hT
    have hU' : kapOfBounded U ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S} := hU
    have step1 : ∀ (a : H →L[ℂ] H), a ∈ (↑S : Set (H →L[ℂ] H)) →
        ∀ (V : H →L[ℂ] H),
          kapOfBounded V ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S} →
          kapOfBounded (a * V) ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S} := by
      intro a ha V hV
      rw [kapOfBounded_mul_post]
      exact map_mem_closure (kapPostcomp_cont a) hV (fun p hp => by
        change toBounded (PointwiseConvergenceCLM.postcomp H a p) ∈ ↑S
        rw [kapToBounded_postcomp]
        exact mul_mem ha hp)
    have hmaps : Set.MapsTo (PointwiseConvergenceCLM.precomp H U)
        {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}
        (closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}) := by
      intro q hq
      have e1 : PointwiseConvergenceCLM.precomp H U q
          = kapOfBounded (toBounded q * U) := by
        rw [kapOfBounded_mul_pre, kapOfBounded_toBounded]
      rw [e1]
      exact step1 _ hq _ hU'
    have hmem := map_mem_closure (kapPrecomp_cont U) hT' hmaps
    rw [closure_closure] at hmem
    change kapOfBounded (T * U) ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}
    rw [kapOfBounded_mul_pre]
    exact hmem
  algebraMap_mem' := by
    intro c
    have hmem : kapOfBounded (algebraMap ℂ (H →L[ℂ] H) c)
        ∈ {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S} := by
      change toBounded (kapOfBounded (algebraMap ℂ (H →L[ℂ] H) c)) ∈ ↑S
      rw [kapToBounded_ofBounded]
      exact S.algebraMap_mem c
    change kapOfBounded (algebraMap ℂ (H →L[ℂ] H) c)
      ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}
    exact subset_closure hmem
  star_mem' := by
    intro x hx
    have hx' : kapOfBounded x ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S} := hx
    have e : kapOfBounded (star x) = kapStar (kapOfBounded x) := by
      unfold kapStar
      rw [kapToBounded_ofBounded]
    change kapOfBounded (star x) ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}
    rw [e]
    exact kapStar_mem_closure_of_convex (kapSotConvex S) (kapSotStar S) hx'

end KapClosure
end Analysis.CStarAlgebra.KaplanskyDensityWanted
