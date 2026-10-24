import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionFold
open Finset StatMech StatMech.FrontierA


/--
[isingDiagonalDomainReflectEquiv_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionFold.lean)
-/
@[path]
private lemma isingDiagonalDomainReflectEquiv_val_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i j : Fin d}
  {c : Int}
  {x : freeDomainVertices K}
-- given
  (hij : i ≠ j)
  (hK : ∀ x : Site d, x ∈ K ↔ isingDiagonalReflect i j c x ∈ K) :
-- imply
  (isingDiagonalDomainReflectEquiv K i j hij c hK x).1 = isingDiagonalReflect i j c x.1 := by
-- proof
  apply StatMech.FrontierA.isingDiagonalDomainReflectEquiv_val K i j hij c hK x

/--
[isingDiagonalDomainReflectEquiv_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionFold.lean)
-/
@[path]
private lemma isingDiagonalDomainReflectEquiv_adj_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i j : Fin d}
  {c : Int}
  {x y : freeDomainVertices K}
-- given
  (hij : i ≠ j)
  (hK : ∀ x : Site d, x ∈ K ↔ isingDiagonalReflect i j c x ∈ K) :
-- imply
  (freeDomainGraph K).Adj x y ↔ (freeDomainGraph K).Adj (isingDiagonalDomainReflectEquiv K i j hij c hK x) (isingDiagonalDomainReflectEquiv K i j hij c hK y) := by
-- proof
  apply StatMech.FrontierA.isingDiagonalDomainReflectEquiv_adj K i j hij c hK x y

/--
[isingDiagonalDomainReflect_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionFold.lean)
-/
@[path]
private lemma isingDiagonalDomainReflect_fixed_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i j : Fin d}
  {c : Int}
  {x : freeDomainVertices K}
-- given
  (hij : i ≠ j)
  (hK : ∀ x : Site d, x ∈ K ↔ isingDiagonalReflect i j c x ∈ K)
  (hx : isingDiagonalDomainPlane K i j c x) :
-- imply
  isingDiagonalDomainReflectEquiv K i j hij c hK x = x := by
-- proof
  apply StatMech.FrontierA.isingDiagonalDomainReflect_fixed K i j hij c hK hx

/--
[isingDiagonalDomainReflect_lower_of_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionFold.lean)
-/
@[path]
private lemma isingDiagonalDomainReflect_lower_of_upper_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i j : Fin d}
  {c : Int}
  {x : freeDomainVertices K}
-- given
  (hij : i ≠ j)
  (hK : ∀ x : Site d, x ∈ K ↔ isingDiagonalReflect i j c x ∈ K)
  (hp : ¬ isingDiagonalDomainPlane K i j c x)
  (hl : ¬ isingDiagonalDomainLower K i j c x) :
-- imply
  isingDiagonalDomainLower K i j c (isingDiagonalDomainReflectEquiv K i j hij c hK x) := by
-- proof
  apply StatMech.FrontierA.isingDiagonalDomainReflect_lower_of_upper K i j hij c hK hp hl

/--
[isingDiagonalDomainReflect_not_plane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionFold.lean)
-/
@[path]
private lemma isingDiagonalDomainReflect_not_plane_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i j : Fin d}
  {c : Int}
  {x : freeDomainVertices K}
-- given
  (hij : i ≠ j)
  (hK : ∀ x : Site d, x ∈ K ↔ isingDiagonalReflect i j c x ∈ K)
  (hp : ¬ isingDiagonalDomainPlane K i j c x) :
-- imply
  ¬ isingDiagonalDomainPlane K i j c (isingDiagonalDomainReflectEquiv K i j hij c hK x) := by
-- proof
  apply StatMech.FrontierA.isingDiagonalDomainReflect_not_plane K i j hij c hK hp

/--
[isingDiagonalDomainReflect_not_lower_of_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionFold.lean)
-/
@[path]
private lemma isingDiagonalDomainReflect_not_lower_of_lower_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i j : Fin d}
  {c : Int}
  {x : freeDomainVertices K}
-- given
  (hij : i ≠ j)
  (hK : ∀ x : Site d, x ∈ K ↔ isingDiagonalReflect i j c x ∈ K)
  (hl : isingDiagonalDomainLower K i j c x) :
-- imply
  ¬ isingDiagonalDomainLower K i j c (isingDiagonalDomainReflectEquiv K i j hij c hK x) := by
-- proof
  apply StatMech.FrontierA.isingDiagonalDomainReflect_not_lower_of_lower K i j hij c hK hl

/--
[isingDiagonalDomainSplit_glue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionFold.lean)
-/
@[path]
private lemma isingDiagonalDomainSplit_glue_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i j : Fin d}
  {c : Int}
  {boundary : ConfigSpace (IsingDiagonalDomainPlane K i j c)}
  {lower upper : ConfigSpace (IsingDiagonalDomainLower K i j c)}
-- given
  (hij : i ≠ j)
  (hK : ∀ x : Site d, x ∈ K ↔ isingDiagonalReflect i j c x ∈ K) :
-- imply
  isingDiagonalDomainSplit K i j hij c hK (isingDiagonalDomainGlue K i j hij c hK boundary lower upper) = (boundary, (lower, upper)) := by
-- proof
  apply StatMech.FrontierA.isingDiagonalDomainSplit_glue K i j hij c hK boundary lower upper

/--
[isingDiagonalDomainGlue_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionFold.lean)
-/
@[path]
private lemma isingDiagonalDomainGlue_split_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i j : Fin d}
  {c : Int}
  {sigma : ConfigSpace (freeDomainVertices K)}
-- given
  (hij : i ≠ j)
  (hK : ∀ x : Site d, x ∈ K ↔ isingDiagonalReflect i j c x ∈ K) :
-- imply
  isingDiagonalDomainGlue K i j hij c hK (isingDiagonalDomainSplit K i j hij c hK sigma).1 (isingDiagonalDomainSplit K i j hij c hK sigma).2.1 (isingDiagonalDomainSplit K i j hij c hK sigma).2.2 = sigma := by
-- proof
  apply StatMech.FrontierA.isingDiagonalDomainGlue_split K i j hij c hK sigma

/--
[isingDiagonalDomainGlue_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionFold.lean)
-/
@[path]
private lemma isingDiagonalDomainGlue_reflect_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i j : Fin d}
  {c : Int}
  {boundary : ConfigSpace (IsingDiagonalDomainPlane K i j c)}
  {lower upper : ConfigSpace (IsingDiagonalDomainLower K i j c)}
-- given
  (hij : i ≠ j)
  (hK : ∀ x : Site d, x ∈ K ↔ isingDiagonalReflect i j c x ∈ K) :
-- imply
  isingCfgEquiv (isingDiagonalDomainReflectEquiv K i j hij c hK) (isingDiagonalDomainGlue K i j hij c hK boundary lower upper) = isingDiagonalDomainGlue K i j hij c hK boundary upper lower := by
-- proof
  apply StatMech.FrontierA.isingDiagonalDomainGlue_reflect K i j hij c hK boundary lower upper

/--
[isingDiagonalDomain_no_lower_upper_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionFold.lean)
-/
@[path]
private lemma isingDiagonalDomain_no_lower_upper_edge_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i j : Fin d}
  {c : Int}
  {x y : freeDomainVertices K}
-- given
  (hij : i ≠ j)
  (hK : ∀ x : Site d, x ∈ K ↔ isingDiagonalReflect i j c x ∈ K)
  (hxy : (freeDomainGraph K).Adj x y)
  (hij0 : i ≠ j) :
-- imply
  ¬ ((isingDiagonalDomainLower K i j c x ∧ ¬ isingDiagonalDomainLower K i j c y ∧ ¬ isingDiagonalDomainPlane K i j c y) ∨ (isingDiagonalDomainLower K i j c y ∧ ¬ isingDiagonalDomainLower K i j c x ∧ ¬ isingDiagonalDomainPlane K i j c x)) := by
-- proof
  apply StatMech.FrontierA.isingDiagonalDomain_no_lower_upper_edge K i j hij c hK hxy hij0

/--
[isingDiagonalDomain_hamiltonian_midpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionFold.lean)
-/
@[path]
private lemma isingDiagonalDomain_hamiltonian_midpoint_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i j : Fin d}
  {c : Int}
  {boundary : ConfigSpace (IsingDiagonalDomainPlane K i j c)}
  {lower upper : ConfigSpace (IsingDiagonalDomainLower K i j c)}
-- given
  (hij : i ≠ j)
  (hK : ∀ x : Site d, x ∈ K ↔ isingDiagonalReflect i j c x ∈ K) :
-- imply
  2 * hamiltonian (freeDomainGraph K) 0 (isingDiagonalDomainGlue K i j hij c hK boundary lower upper) = hamiltonian (freeDomainGraph K) 0 (isingDiagonalDomainGlue K i j hij c hK boundary lower lower) + hamiltonian (freeDomainGraph K) 0 (isingDiagonalDomainGlue K i j hij c hK boundary upper upper) := by
-- proof
  apply StatMech.FrontierA.isingDiagonalDomain_hamiltonian_midpoint K i j hij c hK boundary lower upper

/--
[isingDiagonalDomainWeight_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionFold.lean)
-/
@[path]
private lemma isingDiagonalDomainWeight_factor_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i j : Fin d}
  {c : Int}
  {beta : Real}
  {boundary : ConfigSpace (IsingDiagonalDomainPlane K i j c)}
  {lower upper : ConfigSpace (IsingDiagonalDomainLower K i j c)}
-- given
  (hij : i ≠ j)
  (hK : ∀ x : Site d, x ∈ K ↔ isingDiagonalReflect i j c x ∈ K) :
-- imply
  isingWeight (freeDomainGraph K) beta 0 (isingDiagonalDomainGlue K i j hij c hK boundary lower upper) = isingDiagonalDomainHalfWeight K i j hij c hK beta boundary lower * isingDiagonalDomainHalfWeight K i j hij c hK beta boundary upper := by
-- proof
  apply StatMech.FrontierA.isingDiagonalDomainWeight_factor K i j hij c hK beta boundary lower upper

/--
[isingDiagonalDomainHalfWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionFold.lean)
-/
@[path]
private lemma isingDiagonalDomainHalfWeight_pos_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i j : Fin d}
  {c : Int}
  {beta : Real}
  {boundary : ConfigSpace (IsingDiagonalDomainPlane K i j c)}
  {lower : ConfigSpace (IsingDiagonalDomainLower K i j c)}
-- given
  (hij : i ≠ j)
  (hK : ∀ x : Site d, x ∈ K ↔ isingDiagonalReflect i j c x ∈ K) :
-- imply
  0 < isingDiagonalDomainHalfWeight K i j hij c hK beta boundary lower := by
-- proof
  apply StatMech.FrontierA.isingDiagonalDomainHalfWeight_pos K i j hij c hK beta boundary lower

/--
[isingDiagonalDomainHalfWeight_fkg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionFold.lean)
-/
@[path]
private lemma isingDiagonalDomainHalfWeight_fkg_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i j : Fin d}
  {c : Int}
  {beta : Real}
  {boundary : ConfigSpace (IsingDiagonalDomainPlane K i j c)}
-- given
  (hij : i ≠ j)
  (hK : ∀ x : Site d, x ∈ K ↔ isingDiagonalReflect i j c x ∈ K)
  (hbeta : 0 <= beta) :
-- imply
  FKGLatticeCondition (isingDiagonalDomainHalfWeight K i j hij c hK beta boundary) := by
-- proof
  apply StatMech.FrontierA.isingDiagonalDomainHalfWeight_fkg K i j hij c hK beta hbeta boundary

/--
[isingDiagonalDomain_twoPoint_reflect_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionFold.lean)
-/
@[path]
private lemma isingDiagonalDomain_twoPoint_reflect_le_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i j : Fin d}
  {c : Int}
  {beta : Real}
  {x y : IsingDiagonalDomainLower K i j c}
-- given
  (hij : i ≠ j)
  (hK : ∀ x : Site d, x ∈ K ↔ isingDiagonalReflect i j c x ∈ K)
  (hbeta : 0 <= beta) :
-- imply
  isingExpectation (freeDomainGraph K) beta 0 (fun sigma => spin sigma x.1 * spin sigma (isingDiagonalDomainReflectEquiv K i j hij c hK y.1)) <= isingExpectation (freeDomainGraph K) beta 0 (fun sigma => spin sigma x.1 * spin sigma y.1) := by
-- proof
  apply StatMech.FrontierA.isingDiagonalDomain_twoPoint_reflect_le K i j hij c hK beta hbeta x y

/--
[mem_isingDiagonalSymmetricHull_reflect_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionFold.lean)
-/
@[path]
private lemma mem_isingDiagonalSymmetricHull_reflect_iff_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i j : Fin d}
  {c : Int}
  {x : Site d}
-- given
  (hij : i ≠ j) :
-- imply
  x ∈ isingDiagonalSymmetricHull K i j c ↔ isingDiagonalReflect i j c x ∈ isingDiagonalSymmetricHull K i j c := by
-- proof
  apply StatMech.FrontierA.mem_isingDiagonalSymmetricHull_reflect_iff K i j hij c x

/--
[subset_isingDiagonalSymmetricHull](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionFold.lean)
-/
@[path]
private lemma subset_isingDiagonalSymmetricHull_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i j : Fin d}
  {c : Int} :
-- imply
  K ⊆ isingDiagonalSymmetricHull K i j c := by
-- proof
  apply StatMech.FrontierA.subset_isingDiagonalSymmetricHull K i j c

/--
[freeDomain_spinProd_diagonalReflect_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionFold.lean)
-/
@[path]
private lemma freeDomain_spinProd_diagonalReflect_le_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i j : Fin d}
  {c : Int}
  {beta : Real}
  {a b : Site d}
-- given
  (hij : i ≠ j)
  (hK : ∀ x : Site d, x ∈ K ↔ isingDiagonalReflect i j c x ∈ K)
  (hbeta : 0 <= beta)
  (ha : a ∈ K)
  (hb : b ∈ K)
  (hal : a i - a j < c)
  (hbl : b i - b j < c)
  (hab : a ≠ b)
  (habR : a ≠ isingDiagonalReflect i j c b) :
-- imply
  isingExpectation (freeDomainGraph K) beta 0 (spinProd (freeDomainSpinSupport K {a, isingDiagonalReflect i j c b})) <= isingExpectation (freeDomainGraph K) beta 0 (spinProd (freeDomainSpinSupport K {a, b})) := by
-- proof
  apply StatMech.FrontierA.freeDomain_spinProd_diagonalReflect_le K i j hij c hK beta hbeta a b ha hb hal hbl hab habR


-- created on 2026-10-23
