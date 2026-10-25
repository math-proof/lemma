import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryVerticalFlux.Part3
open Equiv Finset SimpleGraph StatMech.Onsager StatMech.Onsager.BaseCase StatMech StatMech.FrontierD


/--
[finitePeriodicSucc_svFinLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryVerticalFlux.lean)
-/
@[path]
private lemma finitePeriodicSucc_svFinLast_eq
  {N : Nat}
-- given
  (hN : 0 < N) :
-- imply
  finitePeriodicSucc hN (svFinLast hN) = (⟨0, hN⟩ : Fin N) := by
-- proof
  apply StatMech.FrontierD.finitePeriodicSucc_svFinLast hN

/--
[not_even_svFinLast_of_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryVerticalFlux.lean)
-/
@[path]
private lemma not_even_svFinLast_of_even_eq
  {N : Nat}
-- given
  (hN : 0 < N)
  (heven : Even N) :
-- imply
  ¬ Even (svFinLast hN).val := by
-- proof
  apply StatMech.FrontierD.not_even_svFinLast_of_even hN heven

/--
[finZero_ne_svFinLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryVerticalFlux.lean)
-/
@[path]
private lemma finZero_ne_svFinLast_eq
  {N : Nat}
-- given
  (hN : 1 < N) :
-- imply
  (⟨0, Nat.zero_lt_of_lt hN⟩ : Fin N) ≠ svFinLast (Nat.zero_lt_of_lt hN) := by
-- proof
  apply StatMech.FrontierD.finZero_ne_svFinLast hN

/--
[fkMedialVerticalSeamBlackDart_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryVerticalFlux.lean)
-/
@[path]
private lemma fkMedialVerticalSeamBlackDart_fst_eq
  {pairing : FKMedialLoopPairing T}
  {i : Fin T.width} :
-- imply
  (fkMedialVerticalSeamBlackDart pairing i).1.1.1 = i := by
-- proof
  apply StatMech.FrontierD.fkMedialVerticalSeamBlackDart_fst pairing i

/--
[fkMedialVerticalSeamBlackDart_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryVerticalFlux.lean)
-/
@[path]
private lemma fkMedialVerticalSeamBlackDart_injective_eq
  {pairing : FKMedialLoopPairing T} :
-- imply
  Function.Injective (fkMedialVerticalSeamBlackDart pairing) := by
-- proof
  apply StatMech.FrontierD.fkMedialVerticalSeamBlackDart_injective pairing

/--
[fkMedialVerticalSeamBlackDart_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryVerticalFlux.lean)
-/
@[path]
private lemma fkMedialVerticalSeamBlackDart_component_eq
  {pairing : FKMedialLoopPairing T}
  {i : Fin T.width} :
-- imply
  (fkMedialLoopGraph T pairing).connectedComponentMk (fkMedialVerticalSeamBlackDart pairing i).1 = (fkMedialLoopGraph T pairing).connectedComponentMk (fkMedialVerticalSeamDart T i) := by
-- proof
  apply StatMech.FrontierD.fkMedialVerticalSeamBlackDart_component pairing i

/--
[fkMedialLoopCanonicalVerticalFlux_eq_blackCycleContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryVerticalFlux.lean)
-/
@[path]
private lemma fkMedialLoopCanonicalVerticalFlux_eq_blackCycleContribution_eq
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialBlackDart T} :
-- imply
  fkMedialLoopCanonicalVerticalFlux pairing ((fkMedialLoopGraph T pairing).connectedComponentMk d.1) = ∑ e : FKMedialBlackDart T, if (fkMedialBlackBoundaryPerm pairing).SameCycle d e then fkMedialBlackVerticalSeamContribution pairing e else 0 := by
-- proof
  apply StatMech.FrontierD.fkMedialLoopCanonicalVerticalFlux_eq_blackCycleContribution pairing d

/--
[fkRectBlackBoundaryMedialStep_snd_eq_coordinate_sub_wrap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryVerticalFlux.lean)
-/
@[path]
private lemma fkRectBlackBoundaryMedialStep_snd_eq_coordinate_sub_wrap_eq
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialBlackDart T} :
-- imply
  (stepOf (fkRectBlackBoundaryMedialDirection pairing d)).2 = (((fkMedialBlackBoundaryPerm pairing d).1.1.2.val : Nat) : Int) - ((d.1.1.2.val : Nat) : Int) - (T.height : Int) * fkMedialBlackVerticalWrapContribution pairing d := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryMedialStep_snd_eq_coordinate_sub_wrap pairing d

/--
[fkMedialBlackVerticalWrapContribution_seamBlackDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryVerticalFlux.lean)
-/
@[path]
private lemma fkMedialBlackVerticalWrapContribution_seamBlackDart_eq
  {pairing : FKMedialLoopPairing T}
  {i : Fin T.width} :
-- imply
  fkMedialBlackVerticalWrapContribution pairing (fkMedialVerticalSeamBlackDart pairing i) = fkMedialCanonicalVerticalSeamSign T i := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackVerticalWrapContribution_seamBlackDart pairing i

/--
[exists_verticalSeamBlackDart_of_wrapContribution_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryVerticalFlux.lean)
-/
@[path]
private lemma exists_verticalSeamBlackDart_of_wrapContribution_ne_zero_eq
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialBlackDart T}
-- given
  (hwrap : fkMedialBlackVerticalWrapContribution pairing d ≠ 0) :
-- imply
  ∃ i : Fin T.width, fkMedialVerticalSeamBlackDart pairing i = d := by
-- proof
  apply StatMech.FrontierD.exists_verticalSeamBlackDart_of_wrapContribution_ne_zero pairing d hwrap

/--
[fkMedialBlackVerticalSeamContribution_eq_wrapContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryVerticalFlux.lean)
-/
@[path]
private lemma fkMedialBlackVerticalSeamContribution_eq_wrapContribution_eq
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialBlackDart T} :
-- imply
  fkMedialBlackVerticalSeamContribution pairing d = fkMedialBlackVerticalWrapContribution pairing d := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackVerticalSeamContribution_eq_wrapContribution pairing d

/--
[fkRectBlackOrbitVerticalWrapSum_eq_neg_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryVerticalFlux.lean)
-/
@[path]
private lemma fkRectBlackOrbitVerticalWrapSum_eq_neg_winding_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R omega let l := fkRectBlackOrbitList pairing d (∑ i : Fin l.length, fkMedialBlackVerticalWrapContribution pairing (l.get i)) = -(fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitVerticalWrapSum_eq_neg_winding R omega d

/--
[fkMedialBlackCycleWrapContribution_eq_orbitSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryVerticalFlux.lean)
-/
@[path]
private lemma fkMedialBlackCycleWrapContribution_eq_orbitSum_eq
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialBlackDart T} :
-- imply
  (∑ e : FKMedialBlackDart T, if (fkMedialBlackBoundaryPerm pairing).SameCycle d e then fkMedialBlackVerticalWrapContribution pairing e else 0) = ∑ i : Fin (fkRectBlackOrbitList pairing d).length, fkMedialBlackVerticalWrapContribution pairing ((fkRectBlackOrbitList pairing d).get i) := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackCycleWrapContribution_eq_orbitSum pairing d

/--
[fkMedialLoopCanonicalVerticalFlux_eq_neg_blackBoundaryWinding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryVerticalFlux.lean)
-/
@[path]
private lemma fkMedialLoopCanonicalVerticalFlux_eq_neg_blackBoundaryWinding_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R omega fkMedialLoopCanonicalVerticalFlux pairing ((fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk d.1) = -(fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 := by
-- proof
  apply StatMech.FrontierD.fkMedialLoopCanonicalVerticalFlux_eq_neg_blackBoundaryWinding R omega d

/--
[one_le_fkMedialUnorientedVerticalWindingTotal_of_blackBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryVerticalFlux.lean)
-/
@[path]
private lemma one_le_fkMedialUnorientedVerticalWindingTotal_of_blackBoundary_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
-- given
  (hvertical : (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 ≠ 0) :
-- imply
  1 ≤ fkMedialUnorientedVerticalWindingTotal (fkRectConfigurationToMedialPairing R omega) := by
-- proof
  apply StatMech.FrontierD.one_le_fkMedialUnorientedVerticalWindingTotal_of_blackBoundary R omega d hvertical

/--
[one_le_fkMedialUnorientedVerticalWindingTotal_of_boundaryOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryVerticalFlux.lean)
-/
@[path]
private lemma one_le_fkMedialUnorientedVerticalWindingTotal_of_boundaryOrbit_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus}
-- given
  (hvertical : (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega d)).2 ≠ 0) :
-- imply
  1 ≤ fkMedialUnorientedVerticalWindingTotal (fkRectConfigurationToMedialPairing R omega) := by
-- proof
  apply StatMech.FrontierD.one_le_fkMedialUnorientedVerticalWindingTotal_of_boundaryOrbit R omega d hvertical


-- created on 2026-10-23
