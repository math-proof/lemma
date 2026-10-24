import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionDomain
open StatMech StatMech.FrontierA


/--
[isingCoordinateDomainReflectEquiv_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionDomain.lean)
-/
@[path]
private lemma isingCoordinateDomainReflectEquiv_val_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i : Fin d}
  {m : Int}
  {x : freeDomainVertices K}
-- given
  (hK : ∀ x : Site d, x ∈ K ↔ isingCoordinateReflect i m x ∈ K) :
-- imply
  (isingCoordinateDomainReflectEquiv K i m hK x).1 = isingCoordinateReflect i m x.1 := by
-- proof
  apply StatMech.FrontierA.isingCoordinateDomainReflectEquiv_val K i m hK x

/--
[isingCoordinateDomainReflectEquiv_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionDomain.lean)
-/
@[path]
private lemma isingCoordinateDomainReflectEquiv_adj_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i : Fin d}
  {m : Int}
  {x y : freeDomainVertices K}
-- given
  (hK : ∀ x : Site d, x ∈ K ↔ isingCoordinateReflect i m x ∈ K) :
-- imply
  (freeDomainGraph K).Adj x y ↔ (freeDomainGraph K).Adj (isingCoordinateDomainReflectEquiv K i m hK x) (isingCoordinateDomainReflectEquiv K i m hK y) := by
-- proof
  apply StatMech.FrontierA.isingCoordinateDomainReflectEquiv_adj K i m hK x y

/--
[isingCoordinateDomainReflect_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionDomain.lean)
-/
@[path]
private lemma isingCoordinateDomainReflect_fixed_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i : Fin d}
  {m : Int}
  {x : freeDomainVertices K}
-- given
  (hK : ∀ x : Site d, x ∈ K ↔ isingCoordinateReflect i m x ∈ K)
  (hx : isingCoordinateDomainPlane K i m x) :
-- imply
  isingCoordinateDomainReflectEquiv K i m hK x = x := by
-- proof
  apply StatMech.FrontierA.isingCoordinateDomainReflect_fixed K i m hK hx

/--
[isingCoordinateDomainReflect_lower_of_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionDomain.lean)
-/
@[path]
private lemma isingCoordinateDomainReflect_lower_of_upper_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i : Fin d}
  {m : Int}
  {x : freeDomainVertices K}
-- given
  (hK : ∀ x : Site d, x ∈ K ↔ isingCoordinateReflect i m x ∈ K)
  (hp : ¬ isingCoordinateDomainPlane K i m x)
  (hl : ¬ isingCoordinateDomainLower K i m x) :
-- imply
  isingCoordinateDomainLower K i m (isingCoordinateDomainReflectEquiv K i m hK x) := by
-- proof
  apply StatMech.FrontierA.isingCoordinateDomainReflect_lower_of_upper K i m hK hp hl

/--
[isingCoordinateDomainReflect_not_plane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionDomain.lean)
-/
@[path]
private lemma isingCoordinateDomainReflect_not_plane_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i : Fin d}
  {m : Int}
  {x : freeDomainVertices K}
-- given
  (hK : ∀ x : Site d, x ∈ K ↔ isingCoordinateReflect i m x ∈ K)
  (hp : ¬ isingCoordinateDomainPlane K i m x) :
-- imply
  ¬ isingCoordinateDomainPlane K i m (isingCoordinateDomainReflectEquiv K i m hK x) := by
-- proof
  apply StatMech.FrontierA.isingCoordinateDomainReflect_not_plane K i m hK hp

/--
[isingCoordinateDomainReflect_not_lower_of_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionDomain.lean)
-/
@[path]
private lemma isingCoordinateDomainReflect_not_lower_of_lower_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i : Fin d}
  {m : Int}
  {x : freeDomainVertices K}
-- given
  (hK : ∀ x : Site d, x ∈ K ↔ isingCoordinateReflect i m x ∈ K)
  (hl : isingCoordinateDomainLower K i m x) :
-- imply
  ¬ isingCoordinateDomainLower K i m (isingCoordinateDomainReflectEquiv K i m hK x) := by
-- proof
  apply StatMech.FrontierA.isingCoordinateDomainReflect_not_lower_of_lower K i m hK hl

/--
[isingCoordinateDomainSplit_glue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionDomain.lean)
-/
@[path]
private lemma isingCoordinateDomainSplit_glue_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i : Fin d}
  {m : Int}
  {boundary : ConfigSpace (IsingCoordinateDomainPlane K i m)}
  {lower upper : ConfigSpace (IsingCoordinateDomainLower K i m)}
-- given
  (hK : ∀ x : Site d, x ∈ K ↔ isingCoordinateReflect i m x ∈ K) :
-- imply
  isingCoordinateDomainSplit K i m hK (isingCoordinateDomainGlue K i m hK boundary lower upper) = (boundary, (lower, upper)) := by
-- proof
  apply StatMech.FrontierA.isingCoordinateDomainSplit_glue K i m hK boundary lower upper

/--
[isingCoordinateDomainGlue_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionDomain.lean)
-/
@[path]
private lemma isingCoordinateDomainGlue_split_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i : Fin d}
  {m : Int}
  {sigma : ConfigSpace (freeDomainVertices K)}
-- given
  (hK : ∀ x : Site d, x ∈ K ↔ isingCoordinateReflect i m x ∈ K) :
-- imply
  isingCoordinateDomainGlue K i m hK (isingCoordinateDomainSplit K i m hK sigma).1 (isingCoordinateDomainSplit K i m hK sigma).2.1 (isingCoordinateDomainSplit K i m hK sigma).2.2 = sigma := by
-- proof
  apply StatMech.FrontierA.isingCoordinateDomainGlue_split K i m hK sigma

/--
[isingCoordinateDomainGlue_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionDomain.lean)
-/
@[path]
private lemma isingCoordinateDomainGlue_reflect_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i : Fin d}
  {m : Int}
  {boundary : ConfigSpace (IsingCoordinateDomainPlane K i m)}
  {lower upper : ConfigSpace (IsingCoordinateDomainLower K i m)}
-- given
  (hK : ∀ x : Site d, x ∈ K ↔ isingCoordinateReflect i m x ∈ K) :
-- imply
  isingCfgEquiv (isingCoordinateDomainReflectEquiv K i m hK) (isingCoordinateDomainGlue K i m hK boundary lower upper) = isingCoordinateDomainGlue K i m hK boundary upper lower := by
-- proof
  apply StatMech.FrontierA.isingCoordinateDomainGlue_reflect K i m hK boundary lower upper


-- created on 2026-10-23
