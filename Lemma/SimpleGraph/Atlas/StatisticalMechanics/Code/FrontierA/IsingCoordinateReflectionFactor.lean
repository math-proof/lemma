import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionFactor
open Finset StatMech StatMech.FrontierA


/--
[isingCoordinateDomainCrossEdge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionFactor.lean)
-/
@[path]
private lemma isingCoordinateDomainCrossEdge_mem_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i : Fin d}
  {m : Int}
  {z : IsingCoordinateDomainLower K i m}
-- given
  (hK : ∀ x : Site d, x ∈ K ↔ isingCoordinateReflect i m x ∈ K)
  (hz : z ∈ isingCoordinateDomainCrossBoundary K i m hK) :
-- imply
  isingCoordinateDomainCrossEdge K i m hK z ∈ (freeDomainGraph K).edgeFinset := by
-- proof
  apply StatMech.FrontierA.isingCoordinateDomainCrossEdge_mem K i m hK hz

/--
[isingCoordinateDomainCrossEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionFactor.lean)
-/
@[path]
private lemma isingCoordinateDomainCrossEdge_injective_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i : Fin d}
  {m : Int}
-- given
  (hK : ∀ x : Site d, x ∈ K ↔ isingCoordinateReflect i m x ∈ K) :
-- imply
  Function.Injective (isingCoordinateDomainCrossEdge K i m hK) := by
-- proof
  apply StatMech.FrontierA.isingCoordinateDomainCrossEdge_injective K i m hK

/--
[isingCoordinateDomain_hamiltonian_cross_correction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionFactor.lean)
-/
@[path]
private lemma isingCoordinateDomain_hamiltonian_cross_correction_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i : Fin d}
  {m : Int}
  {boundary : ConfigSpace (IsingCoordinateDomainPlane K i m)}
  {lower upper : ConfigSpace (IsingCoordinateDomainLower K i m)}
-- given
  (hK : ∀ x : Site d, x ∈ K ↔ isingCoordinateReflect i m x ∈ K) :
-- imply
  2 * hamiltonian (freeDomainGraph K) 0 (isingCoordinateDomainGlue K i m hK boundary lower upper) = hamiltonian (freeDomainGraph K) 0 (isingCoordinateDomainGlue K i m hK boundary lower lower) + hamiltonian (freeDomainGraph K) 0 (isingCoordinateDomainGlue K i m hK boundary upper upper) + 2 * ∑ z ∈ isingCoordinateDomainCrossBoundary K i m hK, (1 - spin lower z * spin upper z) := by
-- proof
  apply StatMech.FrontierA.isingCoordinateDomain_hamiltonian_cross_correction K i m hK boundary lower upper

/--
[isingCoordinateDomainWeight_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionFactor.lean)
-/
@[path]
private lemma isingCoordinateDomainWeight_factor_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i : Fin d}
  {m : Int}
  {beta : Real}
  {boundary : ConfigSpace (IsingCoordinateDomainPlane K i m)}
  {lower upper : ConfigSpace (IsingCoordinateDomainLower K i m)}
-- given
  (hK : ∀ x : Site d, x ∈ K ↔ isingCoordinateReflect i m x ∈ K) :
-- imply
  isingWeight (freeDomainGraph K) beta 0 (isingCoordinateDomainGlue K i m hK boundary lower upper) = isingCoordinateDomainHalfWeight K i m hK beta boundary lower * isingCoordinateDomainHalfWeight K i m hK beta boundary upper * Real.exp (-beta * (isingCoordinateDomainCrossBoundary K i m hK).card) * Real.exp (beta * ∑ z ∈ isingCoordinateDomainCrossBoundary K i m hK, spin lower z * spin upper z) := by
-- proof
  apply StatMech.FrontierA.isingCoordinateDomainWeight_factor K i m hK beta boundary lower upper


-- created on 2026-10-23
