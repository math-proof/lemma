import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhasePerturbation
open Finset Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexBethePerturbRoot_same](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhasePerturbation.lean)
-/
@[path]
private lemma sixVertexBethePerturbRoot_same_eq
  {n : Nat}
  {p : Fin n → Real}
  {ell : Fin n}
  {eps : Real} :
-- imply
  sixVertexBethePerturbRoot p ell eps ell = eps := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePerturbRoot_same p ell eps

/--
[sixVertexBethePerturbRoot_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhasePerturbation.lean)
-/
@[path]
private lemma sixVertexBethePerturbRoot_ne_eq
  {n : Nat}
  {p : Fin n → Real}
  {ell j : Fin n}
  {eps : Real}
-- given
  (hj : j ≠ ell) :
-- imply
  sixVertexBethePerturbRoot p ell eps j = p j := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePerturbRoot_ne p ell j hj eps

/--
[sixVertexBethePerturbRoot_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhasePerturbation.lean)
-/
@[path]
private lemma sixVertexBethePerturbRoot_zero_eq
  {n : Nat}
  {p : Fin n → Real}
  {ell : Fin n}
-- given
  (hell : p ell = 0) :
-- imply
  sixVertexBethePerturbRoot p ell 0 = p := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePerturbRoot_zero p ell hell

/--
[continuous_sixVertexBethePerturbRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhasePerturbation.lean)
-/
@[path]
private lemma continuous_sixVertexBethePerturbRoot_eq
  {n : Nat}
  {p : Fin n → Real}
  {ell : Fin n} :
-- imply
  Continuous (sixVertexBethePerturbRoot p ell) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexBethePerturbRoot p ell

/--
[continuous_sixVertexBetheCollisionFreeIntervalSum_perturbRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhasePerturbation.lean)
-/
@[path]
private lemma continuous_sixVertexBetheCollisionFreeIntervalSum_perturbRoot_eq
  {n : Nat}
  {N : Nat}
  {c : Real}
  {p : Fin (n + 1) → Real}
  {ell : Fin (n + 1)}
  {x : Fin (n + 1) → Int} :
-- imply
  Continuous (fun eps : Real => sixVertexBetheCollisionFreeIntervalSum N c (fun i => sixVertexBethePhase (sixVertexBethePerturbRoot p ell eps i)) x) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexBetheCollisionFreeIntervalSum_perturbRoot N c p ell x

/--
[sixVertexBetheCollisionFreeIntervalSum_perturbRoot_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhasePerturbation.lean)
-/
@[path]
private lemma sixVertexBetheCollisionFreeIntervalSum_perturbRoot_tendsto_eq
  {n : Nat}
  {N : Nat}
  {c : Real}
  {p : Fin (n + 1) → Real}
  {ell : Fin (n + 1)}
  {x : Fin (n + 1) → Int}
-- given
  (hell : p ell = 0) :
-- imply
  Tendsto (fun eps : Real => sixVertexBetheCollisionFreeIntervalSum N c (fun i => sixVertexBethePhase (sixVertexBethePerturbRoot p ell eps i)) x) (nhdsWithin 0 {0}ᶜ) (nhds (sixVertexBetheCollisionFreeIntervalSum N c (fun i => sixVertexBethePhase (p i)) x)) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheCollisionFreeIntervalSum_perturbRoot_tendsto N c p ell hell x

/--
[sixVertexBethePerturbRoot_comp_perm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhasePerturbation.lean)
-/
@[path]
private lemma sixVertexBethePerturbRoot_comp_perm_eq
  {n : Nat}
  {p : Fin n → Real}
  {ell : Fin n}
  {eps : Real}
  {sigma : Equiv.Perm (Fin n)}
  {i : Fin n} :
-- imply
  sixVertexBethePerturbRoot (fun j => p (sigma j)) (sigma.symm ell) eps i = sixVertexBethePerturbRoot p ell eps (sigma i) := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePerturbRoot_comp_perm p ell eps sigma i

/--
[sixVertexBethePerturbRoot_eventually_phase_ne_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhasePerturbation.lean)
-/
@[path]
private lemma sixVertexBethePerturbRoot_eventually_phase_ne_one_eq
  {n : Nat}
  {p : Fin n → Real}
  {ell : Fin n}
-- given
  (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
-- imply
  ∀ᶠ eps in nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ, ∀ j, sixVertexBethePhase (sixVertexBethePerturbRoot p ell eps j) ≠ 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePerturbRoot_eventually_phase_ne_one p ell hother

/--
[continuous_sixVertexBethePerturbedIntervalTotal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhasePerturbation.lean)
-/
@[path]
private lemma continuous_sixVertexBethePerturbedIntervalTotal_eq
  {n : Nat}
  {N : Nat}
  {c : Real}
  {p : Fin (n + 1) → Real}
  {ell : Fin (n + 1)}
  {x : Fin (n + 1) → Int} :
-- imply
  Continuous (sixVertexBethePerturbedIntervalTotal N c p ell x) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexBethePerturbedIntervalTotal N c p ell x

/--
[SixVertexSatisfiesMultiplicativeBetheEquations.perturbedIntervalTotal_tendsto_physicalAction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhasePerturbation.lean)
-/
@[path]
private lemma perturbedIntervalTotal_tendsto_physicalAction_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {ell : Fin (n + 1)}
  {x : SixVertexSector N (n + 1)}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
  (hell : p ell = 0) :
-- imply
  Tendsto (sixVertexBethePerturbedIntervalTotal N c p ell (sixVertexSectorIntCoordinates x)) (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ) (nhds ((sixVertexSectorTransferComplex N (n + 1) c).mulVec (sixVertexCoordinateBetheWave c p) x)) := by
-- proof
  apply StatMech.FrontierD.SixVertexSatisfiesMultiplicativeBetheEquations.perturbedIntervalTotal_tendsto_physicalAction hc p hp ell hell x

/--
[sixVertexBethePerturbedIntervalTotal_eventuallyEq_wordTotal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhasePerturbation.lean)
-/
@[path]
private lemma sixVertexBethePerturbedIntervalTotal_eventuallyEq_wordTotal_eq
  {n : Nat}
  {N : Nat}
  {c : Real}
  {p : Fin (n + 1) → Real}
  {ell : Fin (n + 1)}
  {x : Fin (n + 1) → Int}
-- given
  (hell : p ell = 0)
  (hopen : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
  (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1)
  (hgap : ∀ i, sixVertexBetheShiftCoordinates N x i < x i) :
-- imply
  sixVertexBethePerturbedIntervalTotal N c p ell x =ᶠ[nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ] sixVertexBethePerturbedWordTotal N c p ell x := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePerturbedIntervalTotal_eventuallyEq_wordTotal N c p ell hell hopen hother x hgap

/--
[SixVertexSatisfiesMultiplicativeBetheEquations.perturbedWordTotal_tendsto_physicalAction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhasePerturbation.lean)
-/
@[path]
private lemma perturbedWordTotal_tendsto_physicalAction_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {ell : Fin (n + 1)}
  {x : SixVertexSector N (n + 1)}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
  (hell : p ell = 0)
  (hopen : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
  (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
-- imply
  Tendsto (sixVertexBethePerturbedWordTotal N c p ell (sixVertexSectorIntCoordinates x)) (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ) (nhds ((sixVertexSectorTransferComplex N (n + 1) c).mulVec (sixVertexCoordinateBetheWave c p) x)) := by
-- proof
  apply StatMech.FrontierD.SixVertexSatisfiesMultiplicativeBetheEquations.perturbedWordTotal_tendsto_physicalAction hc p hp ell hell hopen hother x


-- created on 2026-10-23
