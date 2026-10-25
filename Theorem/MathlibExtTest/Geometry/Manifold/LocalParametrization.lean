/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Geometry/Manifold/LocalParametrization.lean -/


import Def.Geometry.Manifold.LocalParametrization
import Lemma.Set.Manifold.LocalParametrization
open scoped Topology Manifold ContDiff
open Manifold
open MathlibExt.Geometry.Manifold.LocalParametrizationWanted


noncomputable section

namespace MathlibExtTest.Geometry.Manifold.LocalParametrization

-- A coordinate projection has surjective derivative, so its level sets are locally parametrized.
example (x₀ : EuclideanSpace ℝ (Fin 2)) :
    ∃ (U : Set (EuclideanSpace ℝ (Fin 1))) (_ : IsOpen U)
      (u₀ : EuclideanSpace ℝ (Fin 1)) (_ : u₀ ∈ U)
      (φ : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 2)),
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 1 φ ∧
      IsImmersion 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 1 φ ∧
      ∃ V ∈ 𝓝 x₀,
        φ '' (U ∩ φ ⁻¹' V) =
          V ∩ (fun x : EuclideanSpace ℝ (Fin 2) =>
            (EuclideanSpace.single 0 (x 1) : EuclideanSpace ℝ (Fin 1))) ⁻¹'
            {EuclideanSpace.single 0 (x₀ 1)} ∧
        φ u₀ = x₀ := by
  let f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 1) :=
    fun x => EuclideanSpace.single 0 (x 1)
  let Lₗ : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1) :=
    { toFun := f
      map_add' := by
        intro x y
        ext i
        fin_cases i
        simp [f]
      map_smul' := by
        intro c x
        ext i
        fin_cases i
        simp [f] }
  let L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    LinearMap.toContinuousLinearMap Lₗ
  have hLf : (L : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 1)) = f := by
    funext x
    simp [L, Lₗ]
  have hf : ContDiff ℝ 1 f := by
    rw [← hLf]
    exact L.contDiff
  have hderiv : HasFDerivAt f L x₀ := by
    rw [← hLf]
    exact L.hasFDerivAt
  have hreg : Function.Surjective (fderiv ℝ f x₀) := by
    rw [hderiv.fderiv]
    intro y
    refine ⟨EuclideanSpace.single 1 (y 0), ?_⟩
    rw [hLf]
    ext i
    fin_cases i
    simp [f]
  simpa [f] using
    regularLevelSet_localParametrization (k := 1) (m := 1) f hf x₀ hreg

-- The graph lemma recognizes the nonlinear parabola as a global immersion.
example : IsImmersion 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) 1 (fun u : ℝ => (u, u ^ 2)) := by
  apply ContDiff.isImmersion_graph
  fun_prop

end MathlibExtTest.Geometry.Manifold.LocalParametrization
end
