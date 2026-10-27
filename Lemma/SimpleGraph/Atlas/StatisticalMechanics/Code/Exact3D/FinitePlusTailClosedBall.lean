import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall.Part4
open StatMech StatMech.Exact3D StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate


/--
[residual_plus_mul_le_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean)
-/
@[path]
private lemma residual_plus_mul_le_radius_eq
  {n : ℕ}
  {C : FinitePlusTailClosedBallContractionCertificate n α} :
-- imply
  C.residual + C.contraction.c * C.radius ≤ C.radius := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.residual_plus_mul_le_radius C

/--
[mapsClosedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean)
-/
@[path]
private lemma mapsClosedBall_eq
  {n : ℕ}
  {C : FinitePlusTailClosedBallContractionCertificate n α} :
-- imply
  FinitePlusTailState.MapsClosedBall C.contraction.map C.center C.radius := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.mapsClosedBall C

/--
[center_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean)
-/
@[path]
private lemma center_mem_eq
  {n : ℕ}
  {C : FinitePlusTailClosedBallContractionCertificate n α} :
-- imply
  FinitePlusTailState.ClosedBall C.center C.radius C.center := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.center_mem C

/--
[fixedPoint_isFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean)
-/
@[path]
private lemma fixedPoint_isFixed_eq
  {n : ℕ}
  {C : FinitePlusTailClosedBallContractionCertificate n α} :
-- imply
  C.contraction.map C.fixedPoint = C.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.fixedPoint_isFixed C

/--
[fixedPoint_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean)
-/
@[path]
private lemma fixedPoint_mem_eq
  {n : ℕ}
  {C : FinitePlusTailClosedBallContractionCertificate n α} :
-- imply
  FinitePlusTailState.ClosedBall C.center C.radius C.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.fixedPoint_mem C

/--
[fixedPoint_mem_selected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean)
-/
@[path]
private lemma fixedPoint_mem_selected_eq
  {n : ℕ}
  {C : FinitePlusTailClosedBallContractionCertificate n α} :
-- imply
  FinitePlusTailState.ClosedBall C.center C.radius C.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.fixedPoint_mem_selected C

/--
[fixedPoint_mem_of_radius_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean)
-/
@[path]
private lemma fixedPoint_mem_of_radius_le_eq
  {n : ℕ}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {radius' : ℝ}
-- given
  (hradius : C.radius ≤ radius') :
-- imply
  FinitePlusTailState.ClosedBall C.center radius' C.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.fixedPoint_mem_of_radius_le C hradius

/--
[fixedPoint_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean)
-/
@[path]
private lemma fixedPoint_unique_eq
  {n : ℕ}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {x y : FinitePlusTailState n α}
-- given
  (hx : C.contraction.map x = x)
  (hy : C.contraction.map y = y) :
-- imply
  x = y := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.fixedPoint_unique C hx hy

/--
[eq_fixedPoint_of_isFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean)
-/
@[path]
private lemma eq_fixedPoint_of_isFixed_eq
  {n : ℕ}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {x : FinitePlusTailState n α}
-- given
  (hx : C.contraction.map x = x) :
-- imply
  x = C.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.eq_fixedPoint_of_isFixed C hx

/--
[ofFiniteClosedBall_fixedPoint_eq_ofFinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean)
-/
@[path]
private lemma ofFiniteClosedBall_fixedPoint_eq_ofFinite_eq
  {n : ℕ}
  {finiteMap : (Fin n → ℝ) → Fin n → ℝ}
  {C : FiniteContraction.ClosedBallContractionCertificate finiteMap} :
-- imply
  (ofFiniteClosedBall (α := α) C).fixedPoint = FinitePlusTailState.ofFinite (α := α) C.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.ofFiniteClosedBall_fixedPoint_eq_ofFinite C

/--
[exists_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean)
-/
@[path]
private lemma exists_fixedPoint_eq
  {n : ℕ}
  {C : FinitePlusTailClosedBallContractionCertificate n α} :
-- imply
  ∃ p : FinitePlusTailState n α, C.contraction.map p = p ∧ FinitePlusTailState.ClosedBall C.center C.radius p := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.exists_fixedPoint C

/--
[exists_unique_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean)
-/
@[path]
private lemma exists_unique_fixedPoint_eq
  {n : ℕ}
  {C : FinitePlusTailClosedBallContractionCertificate n α} :
-- imply
  ∃! p : FinitePlusTailState n α, C.contraction.map p = p := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.exists_unique_fixedPoint C

/--
[iterate_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean)
-/
@[path]
private lemma iterate_mem_eq
  {n : ℕ}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {x : FinitePlusTailState n α}
  {k : ℕ}
-- given
  (hx : FinitePlusTailState.ClosedBall C.center C.radius x) :
-- imply
  FinitePlusTailState.ClosedBall C.center C.radius (C.contraction.iterate k x) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.iterate_mem C hx k

/--
[iterate_dist_le_pow_mul_of_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean)
-/
@[path]
private lemma iterate_dist_le_pow_mul_of_fixed_eq
  {n : ℕ}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {p : FinitePlusTailState n α}
  {x : FinitePlusTailState n α}
  {k : ℕ}
-- given
  (hp : C.contraction.map p = p) :
-- imply
  (C.contraction.iterate k x).dist p ≤ C.contraction.c ^ k * x.dist p := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.iterate_dist_le_pow_mul_of_fixed C hp x k

/--
[iterate_dist_le_pow_mul_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean)
-/
@[path]
private lemma iterate_dist_le_pow_mul_fixedPoint_eq
  {n : ℕ}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {x : FinitePlusTailState n α}
  {k : ℕ} :
-- imply
  (C.contraction.iterate k x).dist C.fixedPoint ≤ C.contraction.c ^ k * x.dist C.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.iterate_dist_le_pow_mul_fixedPoint C x k

/--
[residual_le_margin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean)
-/
@[path]
private lemma residual_le_margin_eq
  {n : ℕ}
  {C : FinitePlusTailClosedBallContractionCertificate n α} :
-- imply
  C.residual ≤ (1 - C.contraction.c) * C.radius := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.residual_le_margin C

/--
[with_larger_residual_contraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean)
-/
@[path]
private lemma with_larger_residual_contraction_eq
  {n : ℕ}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {residual' : ℝ}
-- given
  (hresidual : C.residual ≤ residual')
  (hbudget : residual' + C.contraction.c * C.radius ≤ C.radius) :
-- imply
  (C.with_larger_residual hresidual hbudget).contraction = C.contraction := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.with_larger_residual_contraction C hresidual hbudget

/--
[with_larger_residual_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean)
-/
@[path]
private lemma with_larger_residual_center_eq
  {n : ℕ}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {residual' : ℝ}
-- given
  (hresidual : C.residual ≤ residual')
  (hbudget : residual' + C.contraction.c * C.radius ≤ C.radius) :
-- imply
  (C.with_larger_residual hresidual hbudget).center = C.center := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.with_larger_residual_center C hresidual hbudget

/--
[with_larger_residual_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean)
-/
@[path]
private lemma with_larger_residual_radius_eq
  {n : ℕ}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {residual' : ℝ}
-- given
  (hresidual : C.residual ≤ residual')
  (hbudget : residual' + C.contraction.c * C.radius ≤ C.radius) :
-- imply
  (C.with_larger_residual hresidual hbudget).radius = C.radius := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.with_larger_residual_radius C hresidual hbudget

/--
[with_larger_residual_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean)
-/
@[path]
private lemma with_larger_residual_residual_eq
  {n : ℕ}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {residual' : ℝ}
-- given
  (hresidual : C.residual ≤ residual')
  (hbudget : residual' + C.contraction.c * C.radius ≤ C.radius) :
-- imply
  (C.with_larger_residual hresidual hbudget).residual = residual' := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.with_larger_residual_residual C hresidual hbudget

/--
[with_larger_residual_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean)
-/
@[path]
private lemma with_larger_residual_fixedPoint_eq
  {n : ℕ}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {residual' : ℝ}
-- given
  (hresidual : C.residual ≤ residual')
  (hbudget : residual' + C.contraction.c * C.radius ≤ C.radius) :
-- imply
  (C.with_larger_residual hresidual hbudget).fixedPoint = C.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.with_larger_residual_fixedPoint C hresidual hbudget

/--
[with_larger_radius_contraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean)
-/
@[path]
private lemma with_larger_radius_contraction_eq
  {n : ℕ}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {radius' : ℝ}
-- given
  (hradius : C.radius ≤ radius') :
-- imply
  (C.with_larger_radius hradius).contraction = C.contraction := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.with_larger_radius_contraction C hradius

/--
[with_larger_radius_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean)
-/
@[path]
private lemma with_larger_radius_center_eq
  {n : ℕ}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {radius' : ℝ}
-- given
  (hradius : C.radius ≤ radius') :
-- imply
  (C.with_larger_radius hradius).center = C.center := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.with_larger_radius_center C hradius

/--
[with_larger_radius_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean)
-/
@[path]
private lemma with_larger_radius_radius_eq
  {n : ℕ}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {radius' : ℝ}
-- given
  (hradius : C.radius ≤ radius') :
-- imply
  (C.with_larger_radius hradius).radius = radius' := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.with_larger_radius_radius C hradius

/--
[with_larger_radius_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean)
-/
@[path]
private lemma with_larger_radius_residual_eq
  {n : ℕ}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {radius' : ℝ}
-- given
  (hradius : C.radius ≤ radius') :
-- imply
  (C.with_larger_radius hradius).residual = C.residual := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.with_larger_radius_residual C hradius

/--
[with_larger_radius_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean)
-/
@[path]
private lemma with_larger_radius_fixedPoint_eq
  {n : ℕ}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {radius' : ℝ}
-- given
  (hradius : C.radius ≤ radius') :
-- imply
  (C.with_larger_radius hradius).fixedPoint = C.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.with_larger_radius_fixedPoint C hradius

/--
[mapsClosedBall_of_radius_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean)
-/
@[path]
private lemma mapsClosedBall_of_radius_le_eq
  {n : ℕ}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {radius' : ℝ}
-- given
  (hradius : C.radius ≤ radius') :
-- imply
  FinitePlusTailState.MapsClosedBall C.contraction.map C.center radius' := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.mapsClosedBall_of_radius_le C hradius

/--
[exists_fixedPoint_of_radius_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean)
-/
@[path]
private lemma exists_fixedPoint_of_radius_le_eq
  {n : ℕ}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {radius' : ℝ}
-- given
  (hradius : C.radius ≤ radius') :
-- imply
  ∃ p : FinitePlusTailState n α, C.contraction.map p = p ∧ FinitePlusTailState.ClosedBall C.center radius' p := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.exists_fixedPoint_of_radius_le C hradius

/--
[iterate_mem_of_radius_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean)
-/
@[path]
private lemma iterate_mem_of_radius_le_eq
  {n : ℕ}
  {C : FinitePlusTailClosedBallContractionCertificate n α}
  {radius' : ℝ}
  {x : FinitePlusTailState n α}
  {k : ℕ}
-- given
  (hradius : C.radius ≤ radius')
  (hx : FinitePlusTailState.ClosedBall C.center radius' x) :
-- imply
  FinitePlusTailState.ClosedBall C.center radius' (C.contraction.iterate k x) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallContractionCertificate.iterate_mem_of_radius_le C hradius hx k


-- created on 2026-10-23
