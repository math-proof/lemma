import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.SurfaceKacWardShiftedBase
open StatMech StatMech.FrontierA


/--
[surfaceQuadraticParity_add_spin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardShiftedBase.lean)
-/
@[path]
private lemma surfaceQuadraticParity_add_spin_eq
  {g : Nat}
  {lambda mu : SurfaceSpinStructure g}
-- given
  (h : SurfaceHomology g) :
-- imply
  surfaceQuadraticParity (lambda + mu) h = surfaceQuadraticParity lambda h + surfaceSpinLinearParity mu h := by
-- proof
  apply StatMech.FrontierA.surfaceQuadraticParity_add_spin lambda mu h

/--
[surfaceQuadraticEvenPolynomial_shift_twist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardShiftedBase.lean)
-/
@[path]
private lemma surfaceQuadraticEvenPolynomial_shift_twist_eq
  {g : Nat}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {edgeClass : Sym2 V → SurfaceHomology g}
  {lambda mu : SurfaceSpinStructure g}
  {weight : Sym2 V → Complex} :
-- imply
  surfaceQuadraticEvenPolynomial G edgeClass lambda (surfaceTwistedEdgeWeight edgeClass mu weight) = surfaceQuadraticEvenPolynomial G edgeClass (lambda + mu) weight := by
-- proof
  apply StatMech.FrontierA.surfaceQuadraticEvenPolynomial_shift_twist G edgeClass lambda mu weight

/--
[surface_twisted_kacWard_det_square_of_shifted_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardShiftedBase.lean)
-/
@[path]
private lemma surface_twisted_kacWard_det_square_of_shifted_base_eq
  {g : Nat}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → Complex}
  {edgeClass : Sym2 V → SurfaceHomology g}
  {lambda : SurfaceSpinStructure g}
  {mu : SurfaceSpinStructure g}
  {weight : Sym2 V → Complex}
-- given
  (hbase : ∀ w : Sym2 V → Complex, (1 - kwGraphTransition G w phase).det = surfaceQuadraticEvenPolynomial G edgeClass lambda w ^ 2) :
-- imply
  (1 - surfaceTwistedKacWardMatrix G phase edgeClass mu weight).det = surfaceQuadraticEvenPolynomial G edgeClass (lambda + mu) weight ^ 2 := by
-- proof
  apply StatMech.FrontierA.surface_twisted_kacWard_det_square_of_shifted_base G phase edgeClass lambda hbase mu weight


-- created on 2026-10-23
