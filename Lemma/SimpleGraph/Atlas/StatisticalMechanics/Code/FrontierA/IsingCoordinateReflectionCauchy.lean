import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionCauchy
open Finset StatMech StatMech.FrontierA


/--
[isingCoordinateDomainHalfReflectionForm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionCauchy.lean)
-/
@[path]
private lemma isingCoordinateDomainHalfReflectionForm_nonneg_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i : Fin d}
  {m : Int}
  {beta : Real}
  {boundary : ConfigSpace (IsingCoordinateDomainPlane K i m)}
  {F : ConfigSpace (IsingCoordinateDomainLower K i m) → Real}
-- given
  (hK : ∀ x : Site d, x ∈ K ↔ isingCoordinateReflect i m x ∈ K)
  (hbeta : 0 <= beta) :
-- imply
  0 <= isingCoordinateDomainHalfReflectionForm K i m hK beta boundary F F := by
-- proof
  apply StatMech.FrontierA.isingCoordinateDomainHalfReflectionForm_nonneg K i m hK beta hbeta boundary F

/--
[isingCoordinateDomainReflectionForm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionCauchy.lean)
-/
@[path]
private lemma isingCoordinateDomainReflectionForm_nonneg_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i : Fin d}
  {m : Int}
  {beta : Real}
  {F : ConfigSpace (IsingCoordinateDomainLower K i m) → Real}
-- given
  (hK : ∀ x : Site d, x ∈ K ↔ isingCoordinateReflect i m x ∈ K)
  (hbeta : 0 <= beta) :
-- imply
  0 <= isingCoordinateDomainReflectionForm K i m hK beta F F := by
-- proof
  apply StatMech.FrontierA.isingCoordinateDomainReflectionForm_nonneg K i m hK beta hbeta F

/--
[isingCoordinateDomainReflectionForm_add_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionCauchy.lean)
-/
@[path]
private lemma isingCoordinateDomainReflectionForm_add_left_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i : Fin d}
  {m : Int}
  {beta : Real}
  {F G H : ConfigSpace (IsingCoordinateDomainLower K i m) → Real}
-- given
  (hK : ∀ x : Site d, x ∈ K ↔ isingCoordinateReflect i m x ∈ K) :
-- imply
  isingCoordinateDomainReflectionForm K i m hK beta (F + G) H = isingCoordinateDomainReflectionForm K i m hK beta F H + isingCoordinateDomainReflectionForm K i m hK beta G H := by
-- proof
  apply StatMech.FrontierA.isingCoordinateDomainReflectionForm_add_left K i m hK beta F G H

/--
[isingCoordinateDomainReflectionForm_smul_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionCauchy.lean)
-/
@[path]
private lemma isingCoordinateDomainReflectionForm_smul_left_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i : Fin d}
  {m : Int}
  {beta t : Real}
  {F G : ConfigSpace (IsingCoordinateDomainLower K i m) → Real}
-- given
  (hK : ∀ x : Site d, x ∈ K ↔ isingCoordinateReflect i m x ∈ K) :
-- imply
  isingCoordinateDomainReflectionForm K i m hK beta (t • F) G = t * isingCoordinateDomainReflectionForm K i m hK beta F G := by
-- proof
  apply StatMech.FrontierA.isingCoordinateDomainReflectionForm_smul_left K i m hK beta t F G

/--
[isingCoordinateDomainReflectionForm_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionCauchy.lean)
-/
@[path]
private lemma isingCoordinateDomainReflectionForm_symm_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i : Fin d}
  {m : Int}
  {beta : Real}
  {F G : ConfigSpace (IsingCoordinateDomainLower K i m) → Real}
-- given
  (hK : ∀ x : Site d, x ∈ K ↔ isingCoordinateReflect i m x ∈ K) :
-- imply
  isingCoordinateDomainReflectionForm K i m hK beta F G = isingCoordinateDomainReflectionForm K i m hK beta G F := by
-- proof
  apply StatMech.FrontierA.isingCoordinateDomainReflectionForm_symm K i m hK beta F G

/--
[isingCoordinateDomainReflectionForm_add_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionCauchy.lean)
-/
@[path]
private lemma isingCoordinateDomainReflectionForm_add_right_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i : Fin d}
  {m : Int}
  {beta : Real}
  {F G H : ConfigSpace (IsingCoordinateDomainLower K i m) → Real}
-- given
  (hK : ∀ x : Site d, x ∈ K ↔ isingCoordinateReflect i m x ∈ K) :
-- imply
  isingCoordinateDomainReflectionForm K i m hK beta F (G + H) = isingCoordinateDomainReflectionForm K i m hK beta F G + isingCoordinateDomainReflectionForm K i m hK beta F H := by
-- proof
  apply StatMech.FrontierA.isingCoordinateDomainReflectionForm_add_right K i m hK beta F G H

/--
[isingCoordinateDomainReflectionForm_smul_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionCauchy.lean)
-/
@[path]
private lemma isingCoordinateDomainReflectionForm_smul_right_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i : Fin d}
  {m : Int}
  {beta t : Real}
  {F G : ConfigSpace (IsingCoordinateDomainLower K i m) → Real}
-- given
  (hK : ∀ x : Site d, x ∈ K ↔ isingCoordinateReflect i m x ∈ K) :
-- imply
  isingCoordinateDomainReflectionForm K i m hK beta F (t • G) = t * isingCoordinateDomainReflectionForm K i m hK beta F G := by
-- proof
  apply StatMech.FrontierA.isingCoordinateDomainReflectionForm_smul_right K i m hK beta t F G

/--
[isingCoordinateDomainReflectionForm_cauchy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionCauchy.lean)
-/
@[path]
private lemma isingCoordinateDomainReflectionForm_cauchy_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i : Fin d}
  {m : Int}
  {beta : Real}
  {F G : ConfigSpace (IsingCoordinateDomainLower K i m) → Real}
-- given
  (hK : ∀ x : Site d, x ∈ K ↔ isingCoordinateReflect i m x ∈ K)
  (hbeta : 0 <= beta) :
-- imply
  isingCoordinateDomainReflectionForm K i m hK beta F G ^ 2 <= isingCoordinateDomainReflectionForm K i m hK beta F F * isingCoordinateDomainReflectionForm K i m hK beta G G := by
-- proof
  apply StatMech.FrontierA.isingCoordinateDomainReflectionForm_cauchy K i m hK beta hbeta F G

/--
[isingCoordinateDomain_twoPoint_reflection_cauchy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionCauchy.lean)
-/
@[path]
private lemma isingCoordinateDomain_twoPoint_reflection_cauchy_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i : Fin d}
  {m : Int}
  {beta : Real}
  {x y : IsingCoordinateDomainLower K i m}
-- given
  (hK : ∀ x : Site d, x ∈ K ↔ isingCoordinateReflect i m x ∈ K)
  (hbeta : 0 <= beta) :
-- imply
  isingExpectation (freeDomainGraph K) beta 0 (fun sigma => spin sigma x.1 * spin sigma (isingCoordinateDomainReflectEquiv K i m hK y.1)) ^ 2 <= isingExpectation (freeDomainGraph K) beta 0 (fun sigma => spin sigma x.1 * spin sigma (isingCoordinateDomainReflectEquiv K i m hK x.1)) * isingExpectation (freeDomainGraph K) beta 0 (fun sigma => spin sigma y.1 * spin sigma (isingCoordinateDomainReflectEquiv K i m hK y.1)) := by
-- proof
  apply StatMech.FrontierA.isingCoordinateDomain_twoPoint_reflection_cauchy K i m hK beta hbeta x y


-- created on 2026-10-23
