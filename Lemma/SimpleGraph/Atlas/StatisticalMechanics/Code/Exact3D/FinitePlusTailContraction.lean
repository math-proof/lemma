import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction
open StatMech StatMech.Exact3D StatMech.Exact3D.SummableTail StatMech.Exact3D.FinitePlusTailState StatMech.Exact3D.FinitePlusTailLipschitzCertificate


/--
[zero_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma zero_coeff_eq
  {a : α} :
-- imply
  (0 : SummableTail α).coeff a = 0 := by
-- proof
  apply StatMech.Exact3D.SummableTail.zero_coeff a

/--
[ext](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma ext_eq
  {u v : SummableTail α}
-- given
  (h : u.coeff = v.coeff) :
-- imply
  u = v := by
-- proof
  apply StatMech.Exact3D.SummableTail.ext h

/--
[summable_abs_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma summable_abs_sub_eq
  {u v : SummableTail α} :
-- imply
  Summable fun a => |u.coeff a - v.coeff a| := by
-- proof
  apply StatMech.Exact3D.SummableTail.summable_abs_sub u v

/--
[norm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma norm_nonneg_eq
  {u : SummableTail α} :
-- imply
  0 ≤ u.norm := by
-- proof
  apply StatMech.Exact3D.SummableTail.norm_nonneg u

/--
[dist_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma dist_nonneg_eq
  {u v : SummableTail α} :
-- imply
  0 ≤ u.dist v := by
-- proof
  apply StatMech.Exact3D.SummableTail.dist_nonneg u v

/--
[dist_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma dist_self_eq
  {u : SummableTail α} :
-- imply
  u.dist u = 0 := by
-- proof
  apply StatMech.Exact3D.SummableTail.dist_self u

/--
[dist_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma dist_zero_eq
  {u : SummableTail α} :
-- imply
  u.dist 0 = u.norm := by
-- proof
  apply StatMech.Exact3D.SummableTail.dist_zero u

/--
[zero_dist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma zero_dist_eq
  {u : SummableTail α} :
-- imply
  (0 : SummableTail α).dist u = u.norm := by
-- proof
  apply StatMech.Exact3D.SummableTail.zero_dist u

/--
[dist_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma dist_comm_eq
  {u v : SummableTail α} :
-- imply
  u.dist v = v.dist u := by
-- proof
  apply StatMech.Exact3D.SummableTail.dist_comm u v

/--
[abs_sub_coeff_le_dist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma abs_sub_coeff_le_dist_eq
  {u v : SummableTail α}
  {a : α} :
-- imply
  |u.coeff a - v.coeff a| ≤ u.dist v := by
-- proof
  apply StatMech.Exact3D.SummableTail.abs_sub_coeff_le_dist u v a

/--
[eq_of_dist_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma eq_of_dist_eq_zero_eq
  {u v : SummableTail α}
-- given
  (h : u.dist v = 0) :
-- imply
  u = v := by
-- proof
  apply StatMech.Exact3D.SummableTail.eq_of_dist_eq_zero h

/--
[dist_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma dist_triangle_eq
  {u v w : SummableTail α} :
-- imply
  u.dist w ≤ u.dist v + v.dist w := by
-- proof
  apply StatMech.Exact3D.SummableTail.dist_triangle u v w

/--
[dist_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma dist_scale_eq
  {c : ℝ}
  {u v : SummableTail α} :
-- imply
  (scale c u).dist (scale c v) = |c| * u.dist v := by
-- proof
  apply StatMech.Exact3D.SummableTail.dist_scale c u v

/--
[norm_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma norm_scale_eq
  {c : ℝ}
  {u : SummableTail α} :
-- imply
  (scale c u).norm = |c| * u.norm := by
-- proof
  apply StatMech.Exact3D.SummableTail.norm_scale c u

/--
[norm_toLpOne_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma norm_toLpOne_sub_eq
  {u v : SummableTail α} :
-- imply
  ‖toLpOne u - toLpOne v‖ = u.dist v := by
-- proof
  apply StatMech.Exact3D.SummableTail.norm_toLpOne_sub u v

/--
[dist_toLpOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma dist_toLpOne_eq
  {u v : SummableTail α} :
-- imply
  Dist.dist (toLpOne u) (toLpOne v) = u.dist v := by
-- proof
  apply StatMech.Exact3D.SummableTail.dist_toLpOne u v

/--
[isometry_toLpOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma isometry_toLpOne_eq :
-- imply
  Isometry (toLpOne : SummableTail α → lp (fun _ : α => ℝ) (1 : ℝ≥0∞)) := by
-- proof
  apply StatMech.Exact3D.SummableTail.isometry_toLpOne

/--
[isUniformEmbedding_equivLpOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma isUniformEmbedding_equivLpOne_eq :
-- imply
  IsUniformEmbedding (equivLpOne : SummableTail α ≃ lp (fun _ : α => ℝ) (1 : ℝ≥0∞)) := by
-- proof
  apply StatMech.Exact3D.SummableTail.isUniformEmbedding_equivLpOne

/--
[ext](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma ext_eq_2
  {n : ℕ}
  {x y : FinitePlusTailState n α}
-- given
  (hfinite : x.finite = y.finite)
  (htail : x.tail = y.tail) :
-- imply
  x = y := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailState.ext hfinite htail

/--
[ofFinite_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma ofFinite_finite_eq
  {n : ℕ}
  {x : Fin n → ℝ} :
-- imply
  (ofFinite (α := α) x).finite = x := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailState.ofFinite_finite x

/--
[ofFinite_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma ofFinite_tail_eq
  {n : ℕ}
  {x : Fin n → ℝ} :
-- imply
  (ofFinite (α := α) x).tail = 0 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailState.ofFinite_tail x

/--
[dist_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma dist_nonneg_eq_2
  {n : ℕ}
  {x y : FinitePlusTailState n α} :
-- imply
  0 ≤ x.dist y := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailState.dist_nonneg x y

/--
[finiteDist_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma finiteDist_nonneg_eq
  {n : ℕ}
  {x y : FinitePlusTailState n α} :
-- imply
  0 ≤ x.finiteDist y := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailState.finiteDist_nonneg x y

/--
[tailDist_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma tailDist_nonneg_eq
  {n : ℕ}
  {x y : FinitePlusTailState n α} :
-- imply
  0 ≤ x.tailDist y := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailState.tailDist_nonneg x y

/--
[ofFinite_finiteDist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma ofFinite_finiteDist_eq
  {n : ℕ}
  {x y : Fin n → ℝ} :
-- imply
  (ofFinite (α := α) x).finiteDist (ofFinite y) = FiniteContraction.l1Dist x y := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailState.ofFinite_finiteDist x y

/--
[ofFinite_tailDist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma ofFinite_tailDist_eq
  {n : ℕ}
  {x y : Fin n → ℝ} :
-- imply
  (ofFinite (α := α) x).tailDist (ofFinite y) = 0 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailState.ofFinite_tailDist x y

/--
[ofFinite_dist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma ofFinite_dist_eq
  {n : ℕ}
  {x y : Fin n → ℝ} :
-- imply
  (ofFinite (α := α) x).dist (ofFinite y) = FiniteContraction.l1Dist x y := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailState.ofFinite_dist x y

/--
[finiteDist_le_dist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma finiteDist_le_dist_eq
  {n : ℕ}
  {x y : FinitePlusTailState n α} :
-- imply
  x.finiteDist y ≤ x.dist y := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailState.finiteDist_le_dist x y

/--
[tailDist_le_dist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma tailDist_le_dist_eq
  {n : ℕ}
  {x y : FinitePlusTailState n α} :
-- imply
  x.tailDist y ≤ x.dist y := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailState.tailDist_le_dist x y

/--
[dist_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma dist_self_eq_2
  {n : ℕ}
  {x : FinitePlusTailState n α} :
-- imply
  x.dist x = 0 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailState.dist_self x

/--
[dist_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma dist_comm_eq_2
  {n : ℕ}
  {x y : FinitePlusTailState n α} :
-- imply
  x.dist y = y.dist x := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailState.dist_comm x y

/--
[dist_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma dist_triangle_eq_2
  {n : ℕ}
  {x y z : FinitePlusTailState n α} :
-- imply
  x.dist z ≤ x.dist y + y.dist z := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailState.dist_triangle x y z

/--
[eq_of_dist_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma eq_of_dist_eq_zero_eq_2
  {n : ℕ}
  {x y : FinitePlusTailState n α}
-- given
  (h : x.dist y = 0) :
-- imply
  x = y := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailState.eq_of_dist_eq_zero h

/--
[lipschitz_equivProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma lipschitz_equivProduct_eq
  {n : ℕ} :
-- imply
  LipschitzWith 1 (equivProduct : FinitePlusTailState n α → FiniteContraction.L1Vector n × SummableTail α) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailState.lipschitz_equivProduct

/--
[lipschitz_equivProduct_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma lipschitz_equivProduct_symm_eq
  {n : ℕ} :
-- imply
  LipschitzWith 2 ((equivProduct : FinitePlusTailState n α ≃ FiniteContraction.L1Vector n × SummableTail α).symm) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailState.lipschitz_equivProduct_symm

/--
[isUniformEmbedding_equivProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma isUniformEmbedding_equivProduct_eq
  {n : ℕ} :
-- imply
  IsUniformEmbedding (equivProduct : FinitePlusTailState n α ≃ FiniteContraction.L1Vector n × SummableTail α) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailState.isUniformEmbedding_equivProduct

/--
[center_mem_closedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma center_mem_closedBall_eq
  {n : ℕ}
  {center : FinitePlusTailState n α}
  {radius : ℝ}
-- given
  (hradius : 0 ≤ radius) :
-- imply
  ClosedBall center radius center := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailState.center_mem_closedBall center hradius

/--
[closedBall_mono_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma closedBall_mono_radius_eq
  {n : ℕ}
  {center x : FinitePlusTailState n α}
  {radius radius' : ℝ}
-- given
  (hx : ClosedBall center radius x)
  (hradius : radius ≤ radius') :
-- imply
  ClosedBall center radius' x := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailState.closedBall_mono_radius hx hradius

/--
[ofFinite_closedBall_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma ofFinite_closedBall_iff_eq
  {n : ℕ}
  {center x : Fin n → ℝ}
  {radius : ℝ} :
-- imply
  ClosedBall (ofFinite (α := α) center) radius (ofFinite x) ↔ FiniteContraction.ClosedBall center radius x := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailState.ofFinite_closedBall_iff

/--
[mixed_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma mixed_lipschitz_eq
  {n : ℕ}
  {C : FinitePlusTailLipschitzCertificate n α} :
-- imply
  ∀ x y, (C.map x).dist (C.map y) ≤ C.c * x.dist y := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailLipschitzCertificate.mixed_lipschitz C

/--
[iterate_contracts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma iterate_contracts_eq
  {n : ℕ}
  {C : FinitePlusTailLipschitzCertificate n α}
  {k : ℕ}
  {x y : FinitePlusTailState n α} :
-- imply
  (C.iterate k x).dist (C.iterate k y) ≤ C.c ^ k * x.dist y := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailLipschitzCertificate.iterate_contracts C k x y

/--
[mapsClosedBall_iterate_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma mapsClosedBall_iterate_mem_eq
  {n : ℕ}
  {C : FinitePlusTailLipschitzCertificate n α}
  {center : FinitePlusTailState n α}
  {radius : ℝ}
  {x : FinitePlusTailState n α}
  {k : ℕ}
-- given
  (hmap : FinitePlusTailState.MapsClosedBall C.map center radius)
  (hx : FinitePlusTailState.ClosedBall center radius x) :
-- imply
  FinitePlusTailState.ClosedBall center radius (C.iterate k x) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailLipschitzCertificate.mapsClosedBall_iterate_mem C hmap hx k

/--
[mapsClosedBall_of_residual_and_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma mapsClosedBall_of_residual_and_lipschitz_eq
  {n : ℕ}
  {C : FinitePlusTailLipschitzCertificate n α}
  {center : FinitePlusTailState n α}
  {radius residual : ℝ}
-- given
  (hresidual : (C.map center).dist center ≤ residual)
  (hradius : residual + C.c * radius ≤ radius) :
-- imply
  FinitePlusTailState.MapsClosedBall C.map center radius := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailLipschitzCertificate.mapsClosedBall_of_residual_and_lipschitz C center hresidual hradius

/--
[contractingWith](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma contractingWith_eq
  {n : ℕ}
  {C : FinitePlusTailLipschitzCertificate n α} :
-- imply
  ContractingWith (⟨C.c, C.c_nonneg⟩ : ℝ≥0) C.map := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailLipschitzCertificate.contractingWith C

/--
[fixedPoint_isFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma fixedPoint_isFixed_eq
  {n : ℕ}
  {C : FinitePlusTailLipschitzCertificate n α} :
-- imply
  C.map C.fixedPoint = C.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailLipschitzCertificate.fixedPoint_isFixed C

/--
[fixedPoint_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma fixedPoint_unique_eq
  {n : ℕ}
  {C : FinitePlusTailLipschitzCertificate n α}
  {x y : FinitePlusTailState n α}
-- given
  (hx : C.map x = x)
  (hy : C.map y = y) :
-- imply
  x = y := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailLipschitzCertificate.fixedPoint_unique C hx hy

/--
[eq_fixedPoint_of_isFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma eq_fixedPoint_of_isFixed_eq
  {n : ℕ}
  {C : FinitePlusTailLipschitzCertificate n α}
  {x : FinitePlusTailState n α}
-- given
  (hx : C.map x = x) :
-- imply
  x = C.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailLipschitzCertificate.eq_fixedPoint_of_isFixed C hx

/--
[exists_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma exists_fixedPoint_eq
  {n : ℕ}
  {C : FinitePlusTailLipschitzCertificate n α} :
-- imply
  ∃ p : FinitePlusTailState n α, C.map p = p := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailLipschitzCertificate.exists_fixedPoint C

/--
[exists_unique_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma exists_unique_fixedPoint_eq
  {n : ℕ}
  {C : FinitePlusTailLipschitzCertificate n α} :
-- imply
  ∃! p : FinitePlusTailState n α, C.map p = p := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailLipschitzCertificate.exists_unique_fixedPoint C

/--
[iterate_eq_of_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma iterate_eq_of_fixed_eq
  {n : ℕ}
  {C : FinitePlusTailLipschitzCertificate n α}
  {x : FinitePlusTailState n α}
  {k : ℕ}
-- given
  (hx : C.map x = x) :
-- imply
  C.iterate k x = x := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailLipschitzCertificate.iterate_eq_of_fixed C hx k

/--
[iterate_dist_le_pow_mul_of_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma iterate_dist_le_pow_mul_of_fixed_eq
  {n : ℕ}
  {C : FinitePlusTailLipschitzCertificate n α}
  {p : FinitePlusTailState n α}
  {x : FinitePlusTailState n α}
  {k : ℕ}
-- given
  (hp : C.map p = p) :
-- imply
  (C.iterate k x).dist p ≤ C.c ^ k * x.dist p := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailLipschitzCertificate.iterate_dist_le_pow_mul_of_fixed C hp x k

/--
[iterate_dist_le_pow_mul_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma iterate_dist_le_pow_mul_fixedPoint_eq
  {n : ℕ}
  {C : FinitePlusTailLipschitzCertificate n α}
  {x : FinitePlusTailState n α}
  {k : ℕ} :
-- imply
  (C.iterate k x).dist C.fixedPoint ≤ C.c ^ k * x.dist C.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailLipschitzCertificate.iterate_dist_le_pow_mul_fixedPoint C x k

/--
[fixedPoint_mem_closedBall_of_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma fixedPoint_mem_closedBall_of_residual_eq
  {n : ℕ}
  {C : FinitePlusTailLipschitzCertificate n α}
  {center : FinitePlusTailState n α}
  {radius residual : ℝ}
-- given
  (hresidual : (C.map center).dist center ≤ residual)
  (hradius : residual + C.c * radius ≤ radius) :
-- imply
  FinitePlusTailState.ClosedBall center radius C.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailLipschitzCertificate.fixedPoint_mem_closedBall_of_residual C center hresidual hradius

/--
[exists_fixedPoint_mem_closedBall_of_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma exists_fixedPoint_mem_closedBall_of_residual_eq
  {n : ℕ}
  {C : FinitePlusTailLipschitzCertificate n α}
  {center : FinitePlusTailState n α}
  {radius residual : ℝ}
-- given
  (hresidual : (C.map center).dist center ≤ residual)
  (hradius : residual + C.c * radius ≤ radius) :
-- imply
  ∃ p : FinitePlusTailState n α, C.map p = p ∧ FinitePlusTailState.ClosedBall center radius p := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailLipschitzCertificate.exists_fixedPoint_mem_closedBall_of_residual C center hresidual hradius

/--
[ofFiniteMap_map_ofFinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma ofFiniteMap_map_ofFinite_eq
  {n : ℕ}
  {finiteMap : (Fin n → ℝ) → Fin n → ℝ}
  {c : ℝ}
  {x : Fin n → ℝ}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hfinite : FiniteContraction.LipschitzWithConstant finiteMap c) :
-- imply
  ((ofFiniteMap (α := α) finiteMap hc_nonneg hc_lt_one hfinite).map (FinitePlusTailState.ofFinite x)) = FinitePlusTailState.ofFinite (α := α) (finiteMap x) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailLipschitzCertificate.ofFiniteMap_map_ofFinite finiteMap hc_nonneg hc_lt_one hfinite x

/--
[l1Dist_scaleFinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean)
-/
@[path]
private lemma l1Dist_scaleFinite_eq
  {n : ℕ}
  {c : ℝ}
  {x y : Fin n → ℝ} :
-- imply
  FiniteContraction.l1Dist (fun i => c * x i) (fun i => c * y i) = |c| * FiniteContraction.l1Dist x y := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailLipschitzCertificate.l1Dist_scaleFinite c x y


-- created on 2026-10-23
