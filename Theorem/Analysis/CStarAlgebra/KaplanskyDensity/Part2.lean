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
import Def.Analysis.CStarAlgebra.KaplanskyDensity.Part2
open scoped PointwiseConvergenceCLM
open Topology


namespace Analysis.CStarAlgebra.KaplanskyDensityWanted

universe u

section KapClosure

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem kapSotSub_mem {S : StarSubalgebra ℂ (H →L[ℂ] H)}
    {p : H →Lₚₜ[ℂ] H} : p ∈ kapSotSub S ↔ toBounded p ∈ ↑S :=
  Submodule.mem_comap

theorem kapSotSub_coe (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    ↑(kapSotSub S) = {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S} := by
  ext p
  exact kapSotSub_mem

/-- The preimage set is convex. -/
theorem kapSotConvex (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    Convex ℝ {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S} := by
  intro x hx y hy a b ha hb hab
  change toBounded (a • x + b • y) ∈ ↑S
  rw [kapToBounded_add, kapReal_smul_sot, kapReal_smul_sot, kapToBounded_smul,
    kapToBounded_smul]
  exact add_mem (S.smul_mem hx _) (S.smul_mem hy _)

/-- The preimage set is `kapStar`-invariant. -/
theorem kapSotStar (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    ∀ p ∈ {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S},
      kapStar p ∈ {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S} := by
  intro p hp
  change toBounded (kapStar p) ∈ ↑S
  rw [kapToBounded_star]
  exact star_mem hp

/-- The carrier of the topological closure is the norm-closure of the preimage. -/
theorem kapTopClosure_coe (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    ↑(Submodule.topologicalClosure (kapSotSub S))
      = closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S} := by
  rw [Submodule.topologicalClosure_coe, kapSotSub_coe]

theorem kapToBounded_postcomp (a : H →L[ℂ] H) (p : H →Lₚₜ[ℂ] H) :
    toBounded (PointwiseConvergenceCLM.postcomp H a p) = a * toBounded p := by
  ext v
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, kapToBounded_apply]
  rfl

omit [CompleteSpace H] in
theorem kapPostcomp_cont (a : H →L[ℂ] H) :
    Continuous ⇑(PointwiseConvergenceCLM.postcomp H a :
      (H →Lₚₜ[ℂ] H) →L[ℂ] (H →Lₚₜ[ℂ] H)) :=
  (PointwiseConvergenceCLM.postcomp H a : _ →L[ℂ] _).cont

omit [CompleteSpace H] in
theorem kapPrecomp_cont (u : H →L[ℂ] H) :
    Continuous ⇑(PointwiseConvergenceCLM.precomp H u :
      (H →Lₚₜ[ℂ] H) →L[ℂ] (H →Lₚₜ[ℂ] H)) :=
  (PointwiseConvergenceCLM.precomp H u : _ →L[ℂ] _).cont

end KapClosure
end Analysis.CStarAlgebra.KaplanskyDensityWanted
