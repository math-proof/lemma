import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripBoundary.Part2
open StatMech StatMech.Universality StatMech.Universality.HexFiniteStripBoundaryData


/--
[raw_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripBoundary.lean)
-/
@[path]
private lemma raw_eq_zero_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V} :
-- imply
  hexFiniteStripRaw B.Fa B.alphaRest B.betaSum B.epsSum B.epsbarSum = 0 := by
-- proof
  apply StatMech.Universality.HexFiniteStripBoundaryData.raw_eq_zero

/--
[boundary_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripBoundary.lean)
-/
@[path]
private lemma boundary_identity_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
-- given
  (hFa : B.Fa = 1) :
-- imply
  hexBdryCl * B.lam + hexBdryCt * B.tau + B.ups = 1 := by
-- proof
  apply StatMech.Universality.HexFiniteStripBoundaryData.boundary_identity hFa

/--
[contour_boundary_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripBoundary.lean)
-/
@[path]
private lemma contour_boundary_identity_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
-- given
  (hFa : B.Fa = 1) :
-- imply
  hexBdryCl * hexContourLambda R.inRegion R.start h0 B.sides hexChi + hexBdryCt * (hexContourTauPlus R.inRegion R.start h0 B.sides hexChi + hexContourTauMinus R.inRegion R.start h0 B.sides hexChi) + hexContourUpsilon R.inRegion R.start h0 B.sides hexChi = 1 := by
-- proof
  apply StatMech.Universality.HexFiniteStripBoundaryData.contour_boundary_identity hFa

/--
[hexFiniteStrip_boundary_identity_scales](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripBoundary.lean)
-/
@[path]
private lemma hexFiniteStrip_boundary_identity_scales_eq
  [DecidableEq V]
  {R : ℕ → HexFiniteRegion}
  {D : ℕ → HexDomain V}
-- given
  (h0 : ℕ → ℤ)
  (P : ∀ v, (D v).InteriorPairing)
  (B : ∀ v, HexFiniteStripBoundaryData (R v) (h0 v) (D v) (P v))
  (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1) :
-- imply
  ∀ v, 1 ≤ v → hexBdryCl * (B v).lam + hexBdryCt * (B v).tau + (B v).ups = 1 := by
-- proof
  apply StatMech.Universality.hexFiniteStrip_boundary_identity_scales R h0 D P B hFa


-- created on 2026-10-23
