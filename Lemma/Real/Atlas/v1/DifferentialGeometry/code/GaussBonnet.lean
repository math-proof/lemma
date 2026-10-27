import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.DifferentialGeometry.code.GaussBonnet.Part7
open Finset Real CombinatorialGaussBonnet SmoothGaussBonnet GaussBonnetBoundary
open Real CombinatorialGaussBonnet
open Real MeasureTheory


namespace CombinatorialGaussBonnet

/--
[combinatorial_gauss_bonnet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/GaussBonnet.lean)
-/
@[path]
lemma combinatorial_gauss_bonnet
  {S : CompactCombinatorialSurface}
  {T : SurfaceTriangulation}
  {T : SurfaceTriangulation} :
-- imply
  Finset.univ.sum T.gaussCurvatureComb = 2 * π * (T.eulerCharacteristic : ℝ) := by
-- proof
  simp only [SurfaceTriangulation.gaussCurvatureComb]
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hangle : Finset.univ.sum (fun v => (T.facesAt v).sum (T.angleAt v)) =
    (Fintype.card T.F : ℝ) * π := by
    have h1 : Finset.univ.sum (fun v => (T.facesAt v).sum (T.angleAt v)) =
      Finset.univ.sum (fun f => (T.verticesOf f).sum (fun v => T.angleAt v f)) := by
      apply Finset.sum_comm'
      intro v f; simp [T.mem_facesAt_iff]
    rw [h1]
    simp only [T.angle_sum_face]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hangle]
  simp only [SurfaceTriangulation.eulerCharacteristic, SurfaceTriangulation.numVertices,
    SurfaceTriangulation.numEdges, SurfaceTriangulation.numFaces]
  have h2E3F : (2 : ℝ) * (Fintype.card T.E : ℝ) = 3 * (Fintype.card T.F : ℝ) := by
    exact_mod_cast T.two_edges_eq_three_faces
  push_cast
  linear_combination π * h2E3F
end CombinatorialGaussBonnet
namespace SmoothGaussBonnet
open Real CombinatorialGaussBonnet


namespace SmoothGaussBonnet

/--
[totalGaussianCurvature_eq_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/GaussBonnet.lean)
-/
@[path]
lemma totalGaussianCurvature_eq_degree
  {M : Set (Fin 3 → ℝ)}
  {τ : Triangulation M}
  {M : CompactSurface} :
-- imply
  M.totalGaussianCurvature = (M.gaussMapDegree : ℝ) * (4 * Real.pi) :=
-- proof
  M.gaussMapDegree_eq

end SmoothGaussBonnet

namespace SmoothGaussBonnet

/--
[eulerCharacteristic_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/GaussBonnet.lean)
-/
@[path]
lemma eulerCharacteristic_eq
  {M : Set (Fin 3 → ℝ)}
  {τ : Triangulation M}
  {M : CompactSurface} :
-- imply
  M.eulerCharacteristic = M.triangulation.eulerCharacteristic :=
-- proof
  rfl
end SmoothGaussBonnet
namespace CompactSurfaceCurvature
open Real MeasureTheory

end SmoothGaussBonnet

namespace GaussBonnetBoundary

/--
[GeodesicTriangleRegion.sum_exterior_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/GaussBonnet.lean)
-/
@[path]
lemma GeodesicTriangleRegion.sum_exterior_eq
  {D : DiscRegion}
  {Δ : GeodesicTriangleRegion} :
-- imply
  Δ.toDiscRegion.sumExteriorAngles = 3 * π - (Δ.angle₁ + Δ.angle₂ + Δ.angle₃) := by
-- proof
  simp only [DiscRegion.sumExteriorAngles]
  have hconv : ∑ i : Fin Δ.toDiscRegion.numCorners, Δ.toDiscRegion.exteriorAngles i =
    ∑ i : Fin 3, Δ.toDiscRegion.exteriorAngles (Fin.cast Δ.corners_eq.symm i) :=
    Fintype.sum_equiv (finCongr Δ.corners_eq) _ _ (fun i => by simp [finCongr, Fin.cast])
  rw [hconv, Fin.sum_univ_three, Δ.ext_angle_0, Δ.ext_angle_1, Δ.ext_angle_2]
  ring

end GaussBonnetBoundary


-- created on 2026-10-23
