/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Geometry/Euclidean/Viviani.lean -/


import Lemma.Set.Euclidean.Viviani
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.LinearAlgebra.AffineSpace.MidpointZero
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

example
    (A B C P Q : EuclideanSpace ℝ (Fin 2))
    (hABBC : dist A B = dist B C)
    (hBCCA : dist B C = dist C A)
    (hpos : 0 < dist A B)
    (hP : P ∈ interior (convexHull ℝ {A, B, C}))
    (hQ : Q ∈ interior (convexHull ℝ {A, B, C})) :
    Metric.infDist P ↑(affineSpan ℝ {A, B}) +
        Metric.infDist P ↑(affineSpan ℝ {B, C}) +
        Metric.infDist P ↑(affineSpan ℝ {C, A}) =
      Metric.infDist Q ↑(affineSpan ℝ {A, B}) +
        Metric.infDist Q ↑(affineSpan ℝ {B, C}) +
        Metric.infDist Q ↑(affineSpan ℝ {C, A}) := by
  exact
    (MetaMathlibExt.viviani A B C P hABBC hBCCA hpos hP).trans
      (MetaMathlibExt.viviani A B C Q hABBC hBCCA hpos hQ).symm

example :
    let A : EuclideanSpace ℝ (Fin 2) := !₂[(0 : ℝ), 0]
    let B : EuclideanSpace ℝ (Fin 2) := !₂[(2 : ℝ), 0]
    let C : EuclideanSpace ℝ (Fin 2) := !₂[(1 : ℝ), Real.sqrt 3]
    let G : EuclideanSpace ℝ (Fin 2) := !₂[(1 : ℝ), Real.sqrt 3 / 3]
    Metric.infDist G ↑(affineSpan ℝ {A, B}) +
        Metric.infDist G ↑(affineSpan ℝ {B, C}) +
        Metric.infDist G ↑(affineSpan ℝ {C, A}) =
      Real.sqrt 3 := by
  let A : EuclideanSpace ℝ (Fin 2) := !₂[(0 : ℝ), 0]
  let B : EuclideanSpace ℝ (Fin 2) := !₂[(2 : ℝ), 0]
  let C : EuclideanSpace ℝ (Fin 2) := !₂[(1 : ℝ), Real.sqrt 3]
  let G : EuclideanSpace ℝ (Fin 2) := !₂[(1 : ℝ), Real.sqrt 3 / 3]
  change Metric.infDist G ↑(affineSpan ℝ {A, B}) +
      Metric.infDist G ↑(affineSpan ℝ {B, C}) +
      Metric.infDist G ↑(affineSpan ℝ {C, A}) =
    Real.sqrt 3
  have hsides : dist A B = 2 ∧ dist B C = 2 ∧ dist C A = 2 ∧ 0 < dist A B := by
    dsimp [A, B, C]
    norm_num [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.sq_sqrt,
      Real.sqrt_eq_iff_eq_sq]
  rcases hsides with ⟨hAB, hBC, hCA, hpos⟩
  let p : Fin 3 → EuclideanSpace ℝ (Fin 2) := ![A, B, C]
  have hAI : AffineIndependent ℝ p := by
    rw [affineIndependent_iff_of_fintype]
    intro w hw hweighted i
    rw [Finset.weightedVSub_eq_linear_combination Finset.univ hw] at hweighted
    have hx : 2 * w 1 + w 2 = 0 := by
      simpa [p, A, B, C, Fin.sum_univ_three, mul_comm] using
        congrArg (fun q : EuclideanSpace ℝ (Fin 2) ↦ q 0) hweighted
    have hy : w 2 * Real.sqrt 3 = 0 := by
      simpa [p, A, B, C, Fin.sum_univ_three] using
        congrArg (fun q : EuclideanSpace ℝ (Fin 2) ↦ q 1) hweighted
    have hsqrt : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    have hw2 : w 2 = 0 := (mul_eq_zero.mp hy).resolve_right hsqrt
    have hw1 : w 1 = 0 := by linarith
    have hw0 : w 0 = 0 := by simpa [Fin.sum_univ_three, hw1, hw2] using hw
    fin_cases i <;> assumption
  have hspan : affineSpan ℝ (Set.range p) = ⊤ := by
    rw [hAI.affineSpan_eq_top_iff_card_eq_finrank_add_one]
    norm_num [finrank_euclideanSpace]
  let b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)) := ⟨p, hAI, hspan⟩
  have hrange : Set.range b = {A, B, C} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      change p i = _ ∨ p i = _ ∨ p i = _
      fin_cases i <;> simp [p]
    · intro hx
      rcases hx with rfl | rfl | rfl
      · refine ⟨0, ?_⟩
        change p 0 = _
        simp [p]
      · refine ⟨1, ?_⟩
        change p 1 = _
        simp [p]
      · refine ⟨2, ?_⟩
        change p 2 = _
        simp [p]
  have hcentroid : Finset.univ.centroid ℝ b = G := by
    change Finset.univ.centroid ℝ p = G
    have hweights :
        ∑ i ∈ Finset.univ, (Finset.univ.centroidWeights ℝ : Fin 3 → ℝ) i = 1 := by
      norm_num [Fin.sum_univ_three]
    rw [Finset.centroid_def,
      Finset.affineCombination_eq_linear_combination Finset.univ _ _ hweights]
    ext i
    fin_cases i
    · norm_num [p, A, B, C, G, Fin.sum_univ_three]
    · norm_num [p, A, B, C, G, Fin.sum_univ_three]
      ring
  have hG : G ∈ interior (convexHull ℝ {A, B, C}) := by
    rw [← hcentroid, ← hrange]
    exact b.centroid_mem_interior_convexHull
  have hABAC : dist A B = dist A C :=
    hAB.trans ((dist_comm A C).trans hCA).symm
  have hheight : Metric.infDist A ↑(affineSpan ℝ {B, C}) = Real.sqrt 3 := by
    let L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) := affineSpan ℝ {B, C}
    have hmid : midpoint ℝ B C ∈ L := by
      rw [← lineMap_inv_two]
      exact AffineMap.lineMap_mem_affineSpan_pair _ _ _
    have hperp : A ∈ AffineSubspace.perpBisector B C :=
      AffineSubspace.mem_perpBisector_iff_dist_eq.mpr hABAC
    have horth : A -ᵥ midpoint ℝ B C ∈ L.directionᗮ := by
      change A -ᵥ midpoint ℝ B C ∈ (affineSpan ℝ {B, C}).directionᗮ
      rw [direction_affineSpan, vectorSpan_pair_rev,
        Submodule.mem_orthogonal_singleton_iff_inner_right]
      exact AffineSubspace.mem_perpBisector_iff_inner_eq_zero'.mp hperp
    have hproj :
        (EuclideanGeometry.orthogonalProjection L A : EuclideanSpace ℝ (Fin 2)) =
          midpoint ℝ B C :=
      EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem.mpr ⟨hmid, horth⟩
    have hfoot : midpoint ℝ B C = !₂[(3 / 2 : ℝ), Real.sqrt 3 / 2] := by
      ext i
      fin_cases i
      · norm_num [B, C, midpoint_eq_smul_add]
      · norm_num [B, C, midpoint_eq_smul_add]
        ring
    have hdist : dist A (midpoint ℝ B C) = Real.sqrt 3 := by
      rw [hfoot]
      dsimp [A]
      norm_num [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.sq_sqrt,
        Real.sqrt_eq_iff_eq_sq]
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    change Metric.infDist A (L : Set (EuclideanSpace ℝ (Fin 2))) = _
    rw [← EuclideanGeometry.dist_orthogonalProjection_eq_infDist L A, hproj, hdist]
  exact
    (MetaMathlibExt.viviani A B C G
      (hAB.trans hBC.symm) (hBC.trans hCA.symm) hpos hG).trans hheight
