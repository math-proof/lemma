import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.FKTrihexDuality
open StatMech StatMech.FrontierA


/--
[triangularFKCriticalSurface_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FKTrihexDuality.lean)
-/
@[path]
private lemma triangularFKCriticalSurface_diagonal_eq
  {q y : ℝ} :
-- imply
  triangularFKCriticalSurface q y y y = triangularFKCriticalPolynomial q y := by
-- proof
  apply StatMech.FrontierA.triangularFKCriticalSurface_diagonal q y

/--
[hexagonalFKCriticalSurface_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FKTrihexDuality.lean)
-/
@[path]
private lemma hexagonalFKCriticalSurface_diagonal_eq
  {q y : ℝ} :
-- imply
  hexagonalFKCriticalSurface q y y y = hexagonalFKCriticalPolynomial q y := by
-- proof
  apply StatMech.FrontierA.hexagonalFKCriticalSurface_diagonal q y

/--
[trihex_dual_surface_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FKTrihexDuality.lean)
-/
@[path]
private lemma trihex_dual_surface_identity_eq
  {q y0 y1 y2 y0Star y1Star y2Star : ℝ}
-- given
  (h0 : y0 * y0Star = q)
  (h1 : y1 * y1Star = q)
  (h2 : y2 * y2Star = q) :
-- imply
  (y0 * y1 * y2) * hexagonalFKCriticalSurface q y0Star y1Star y2Star = -(q ^ 2) * triangularFKCriticalSurface q y0 y1 y2 := by
-- proof
  apply StatMech.FrontierA.trihex_dual_surface_identity h0 h1 h2

/--
[hexagonalFKCriticalSurface_of_dual_triangular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FKTrihexDuality.lean)
-/
@[path]
private lemma hexagonalFKCriticalSurface_of_dual_triangular_eq
  {q y0 y1 y2 y0Star y1Star y2Star : ℝ}
-- given
  (hy0 : y0 ≠ 0)
  (hy1 : y1 ≠ 0)
  (hy2 : y2 ≠ 0)
  (h0 : y0 * y0Star = q)
  (h1 : y1 * y1Star = q)
  (h2 : y2 * y2Star = q)
  (htri : triangularFKCriticalSurface q y0 y1 y2 = 0) :
-- imply
  hexagonalFKCriticalSurface q y0Star y1Star y2Star = 0 := by
-- proof
  apply StatMech.FrontierA.hexagonalFKCriticalSurface_of_dual_triangular hy0 hy1 hy2 h0 h1 h2 htri

/--
[triangularFKCriticalSurface_of_dual_hexagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FKTrihexDuality.lean)
-/
@[path]
private lemma triangularFKCriticalSurface_of_dual_hexagonal_eq
  {q y0 y1 y2 y0Star y1Star y2Star : ℝ}
-- given
  (hq : q ≠ 0)
  (h0 : y0 * y0Star = q)
  (h1 : y1 * y1Star = q)
  (h2 : y2 * y2Star = q)
  (hhex : hexagonalFKCriticalSurface q y0Star y1Star y2Star = 0) :
-- imply
  triangularFKCriticalSurface q y0 y1 y2 = 0 := by
-- proof
  apply StatMech.FrontierA.triangularFKCriticalSurface_of_dual_hexagonal hq h0 h1 h2 hhex

/--
[triangularFKCriticalSurface_iff_hexagonal_of_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FKTrihexDuality.lean)
-/
@[path]
private lemma triangularFKCriticalSurface_iff_hexagonal_of_dual_eq
  {q y0 y1 y2 y0Star y1Star y2Star : ℝ}
-- given
  (hq : q ≠ 0)
  (hy0 : y0 ≠ 0)
  (hy1 : y1 ≠ 0)
  (hy2 : y2 ≠ 0)
  (h0 : y0 * y0Star = q)
  (h1 : y1 * y1Star = q)
  (h2 : y2 * y2Star = q) :
-- imply
  triangularFKCriticalSurface q y0 y1 y2 = 0 ↔ hexagonalFKCriticalSurface q y0Star y1Star y2Star = 0 := by
-- proof
  apply StatMech.FrontierA.triangularFKCriticalSurface_iff_hexagonal_of_dual hq hy0 hy1 hy2 h0 h1 h2

/--
[triangularFKCriticalSurface_iff_hexagonal_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FKTrihexDuality.lean)
-/
@[path]
private lemma triangularFKCriticalSurface_iff_hexagonal_div_eq
  {q y0 y1 y2 : ℝ}
-- given
  (hq : q ≠ 0)
  (hy0 : y0 ≠ 0)
  (hy1 : y1 ≠ 0)
  (hy2 : y2 ≠ 0) :
-- imply
  triangularFKCriticalSurface q y0 y1 y2 = 0 ↔ hexagonalFKCriticalSurface q (q / y0) (q / y1) (q / y2) = 0 := by
-- proof
  apply StatMech.FrontierA.triangularFKCriticalSurface_iff_hexagonal_div hq hy0 hy1 hy2

/--
[fkEdgeOdds_mul_dualParam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FKTrihexDuality.lean)
-/
@[path]
private lemma fkEdgeOdds_mul_dualParam_eq
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  fkEdgeOdds p * fkEdgeOdds (BeffaraDC.dualParam p q) = q := by
-- proof
  apply StatMech.FrontierA.fkEdgeOdds_mul_dualParam hp hp1 hq

/--
[triangularFKCriticalSurface_iff_hexagonal_dualParam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FKTrihexDuality.lean)
-/
@[path]
private lemma triangularFKCriticalSurface_iff_hexagonal_dualParam_eq
  {p0 p1 p2 q : ℝ}
-- given
  (hp0 : p0 ∈ Set.Ioo (0 : ℝ) 1)
  (hp1 : p1 ∈ Set.Ioo (0 : ℝ) 1)
  (hp2 : p2 ∈ Set.Ioo (0 : ℝ) 1)
  (hq : 0 < q) :
-- imply
  triangularFKCriticalSurface q (fkEdgeOdds p0) (fkEdgeOdds p1) (fkEdgeOdds p2) = 0 ↔ hexagonalFKCriticalSurface q (fkEdgeOdds (BeffaraDC.dualParam p0 q)) (fkEdgeOdds (BeffaraDC.dualParam p1 q)) (fkEdgeOdds (BeffaraDC.dualParam p2 q)) = 0 := by
-- proof
  apply StatMech.FrontierA.triangularFKCriticalSurface_iff_hexagonal_dualParam hp0 hp1 hp2 hq

/--
[triangularFKCriticalSurface_one_iff_isCriticalTri](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FKTrihexDuality.lean)
-/
@[path]
private lemma triangularFKCriticalSurface_one_iff_isCriticalTri_eq
  {p0 p1 p2 : ℝ}
-- given
  (hp0 : p0 ≠ 1)
  (hp1 : p1 ≠ 1)
  (hp2 : p2 ≠ 1) :
-- imply
  triangularFKCriticalSurface 1 (fkEdgeOdds p0) (fkEdgeOdds p1) (fkEdgeOdds p2) = 0 ↔ Universality.IsCriticalTri p0 p1 p2 := by
-- proof
  apply StatMech.FrontierA.triangularFKCriticalSurface_one_iff_isCriticalTri hp0 hp1 hp2

/--
[hexagonalFKCriticalSurface_one_iff_isCriticalHex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FKTrihexDuality.lean)
-/
@[path]
private lemma hexagonalFKCriticalSurface_one_iff_isCriticalHex_eq
  {p0 p1 p2 : ℝ}
-- given
  (hp0 : p0 ≠ 1)
  (hp1 : p1 ≠ 1)
  (hp2 : p2 ≠ 1) :
-- imply
  hexagonalFKCriticalSurface 1 (fkEdgeOdds p0) (fkEdgeOdds p1) (fkEdgeOdds p2) = 0 ↔ Universality.IsCriticalHex p0 p1 p2 := by
-- proof
  apply StatMech.FrontierA.hexagonalFKCriticalSurface_one_iff_isCriticalHex hp0 hp1 hp2


-- created on 2026-10-23
