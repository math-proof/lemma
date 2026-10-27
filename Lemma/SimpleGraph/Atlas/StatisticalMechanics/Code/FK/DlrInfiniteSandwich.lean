import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.DlrInfiniteSandwich
open MeasureTheory Filter Set StatMech StatMech.FK


/--
[dlr_box_mixture_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DlrInfiniteSandwich.lean)
-/
@[path]
private lemma dlr_box_mixture_sandwich_eq
  {d n : ℕ}
  {p q : ℝ}
  {phi : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
  {A : Set (ConfigSpace (Sym2 (boxVerts d n)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hDLR : IsFKDLR d p q phi)
  (hA : IsIncreasing A) :
-- imply
  dlrBcEventMass (boxGraph d n) (⊥ : SimpleGraph (boxVerts d n)) p q A ≤ (phi : Measure _).real (boxRestrict d n ⁻¹' A) ∧ (phi : Measure _).real (boxRestrict d n ⁻¹' A) ≤ dlrBcEventMass (boxGraph d n) (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d n)) p q A := by
-- proof
  apply StatMech.FK.dlr_box_mixture_sandwich hp hp1 hq hDLR hA

/--
[dlr_infinite_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DlrInfiniteSandwich.lean)
-/
@[path]
private lemma dlr_infinite_sandwich_eq
  {d N : ℕ}
  {p q : ℝ}
  {phi : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
  {A : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hDLR : IsFKDLR d p q phi)
  (hA : IsIncreasing A) :
-- imply
  (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' A) ≤ (phi : Measure _).real (boxRestrict d N ⁻¹' A) ∧ (phi : Measure _).real (boxRestrict d N ⁻¹' A) ≤ (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' A) := by
-- proof
  apply StatMech.FK.dlr_infinite_sandwich hp hp1 hq hDLR hA


-- created on 2026-10-23
