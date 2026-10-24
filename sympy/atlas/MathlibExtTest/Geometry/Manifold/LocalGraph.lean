/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Geometry/Manifold/LocalGraph.lean -/


import sympy.atlas.Geometry.Manifold.LocalGraph
import Lemma.Set.Manifold.LocalGraph

open MathlibExt.Geometry.Manifold.LocalGraphWanted
open scoped Topology

-- The public theorem makes each local level set a graph over the first coordinate.
example
    {E G F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hdim : Module.finrank ℝ E = Module.finrank ℝ G + Module.finrank ℝ F)
    (f : E → F) (hf : ContDiff ℝ 1 f) (x₀ : E)
    (hreg : Function.Surjective (fderiv ℝ f x₀)) :
    ∃ (e : E ≃L[ℝ] G × F) (V : Set E), V ∈ 𝓝 x₀ ∧
      ∀ ⦃x y : E⦄, x ∈ V → x ∈ f ⁻¹' {f x₀} → y ∈ V → y ∈ f ⁻¹' {f x₀} →
        (e x).1 = (e y).1 → x = y := by
  obtain ⟨e, U, -, g, -, V, hV, hgraph⟩ :=
    ContDiff.exists_localGraph_of_surjective_fderiv hdim f hf x₀ hreg
  refine ⟨e, V, hV, ?_⟩
  intro x y hxV hxlevel hyV hylevel hfirst
  have hxGraph : x ∈ V ∩ e ⁻¹' {p : G × F | p.1 ∈ U ∧ p.2 = g p.1} := by
    rw [← hgraph]
    exact ⟨hxV, hxlevel⟩
  have hyGraph : y ∈ V ∩ e ⁻¹' {p : G × F | p.1 ∈ U ∧ p.2 = g p.1} := by
    rw [← hgraph]
    exact ⟨hyV, hylevel⟩
  apply e.injective
  apply Prod.ext
  · exact hfirst
  · calc
      (e x).2 = g (e x).1 := hxGraph.2.2
      _ = g (e y).1 := congrArg g hfirst
      _ = (e y).2 := hyGraph.2.2.symm

-- The frozen Euclidean theorem puts the base point on its local graph at k = m = 1.
example
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 1))
    (hf : ContDiff ℝ 1 f)
    (x₀ : EuclideanSpace ℝ (Fin 2))
    (hreg : Function.Surjective (fderiv ℝ f x₀)) :
    ∃ (e : EuclideanSpace ℝ (Fin 2) ≃L[ℝ]
        EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
      (U : Set (EuclideanSpace ℝ (Fin 1)))
      (g : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)),
      U ∈ 𝓝 (e x₀).1 ∧ ContDiffOn ℝ 1 g U ∧
        (e x₀).1 ∈ U ∧ (e x₀).2 = g (e x₀).1 := by
  obtain ⟨e, U, hU, g, hg, V, hV, hgraph⟩ :=
    regularLevelSet_localGraph (k := 1) (m := 1) f hf x₀ hreg
  have hxGraph : x₀ ∈ V ∩ e ⁻¹' {p | p.1 ∈ U ∧ p.2 = g p.1} := by
    rw [← hgraph]
    exact ⟨mem_of_mem_nhds hV, by simp⟩
  exact ⟨e, U, g, hU, hg, hxGraph.2⟩
