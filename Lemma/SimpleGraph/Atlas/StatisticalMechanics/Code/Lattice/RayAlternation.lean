import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.RayAlternation
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[ral_oddRay_iff_oddCross_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RayAlternation.lean)
-/
@[path]
private lemma ral_oddRay_iff_oddCross_leftRegion_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z₀ q : Site 2}
  {γ : (hypercubicLattice 2).Walk z₀ q}
-- given
  (hq : ∀ p ∈ Vc.support, q 0 ≤ p 0) :
-- imply
  (¬ Even (jec_rayCount z₀ Vc)) ↔ (¬ Even (crossCount (jec_leftRegion Vc) γ)) := by
-- proof
  apply StatMech.Lattice.ral_oddRay_iff_oddCross_leftRegion Vc hq γ

/--
[ral_inRegion_rayCount_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RayAlternation.lean)
-/
@[path]
private lemma ral_inRegion_rayCount_odd_eq
  {K : Set (Site 2)}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z₀ q : Site 2}
  {γ : (hypercubicLattice 2).Walk z₀ q}
-- given
  (hmatch : pww_BdEdgeMatch K Vc)
  (hz₀K : z₀ ∈ K)
  (hqK : q ∉ K)
  (hqfar : ∀ p ∈ Vc.support, q 0 ≤ p 0) :
-- imply
  ¬ Even (jec_rayCount z₀ Vc) := by
-- proof
  apply StatMech.Lattice.ral_inRegion_rayCount_odd Vc hmatch hz₀K hqK hqfar γ

/--
[ral_tailOdd_of_bdEdgeMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RayAlternation.lean)
-/
@[path]
private lemma ral_tailOdd_of_bdEdgeMatch_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {q : Site 2}
  {γ : (hypercubicLattice 2).Walk a.1.tail q}
-- given
  (hK : K.Finite)
  (hmatch : pww_BdEdgeMatch K (olb_orbitLoop K hK a.1 a.2))
  (hqK : q ∉ K)
  (hqfar : ∀ p ∈ (olb_orbitLoop K hK a.1 a.2).support, q 0 ≤ p 0) :
-- imply
  wwit_TailOdd K hK a := by
-- proof
  apply StatMech.Lattice.ral_tailOdd_of_bdEdgeMatch K hK a hmatch hqK hqfar γ

/--
[ral_starHull_tailOdd_of_bdEdgeMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RayAlternation.lean)
-/
@[path]
private lemma ral_starHull_tailOdd_of_bdEdgeMatch_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
  {q : Site 2}
  {γ : (hypercubicLattice 2).Walk a.1.tail q}
-- given
  (hSK : (ndt_StarHull K).Finite)
  (hmatch : pww_BdEdgeMatch (ndt_StarHull K) (olb_orbitLoop (ndt_StarHull K) hSK a.1 a.2))
  (hqK : q ∉ ndt_StarHull K)
  (hqfar : ∀ p ∈ (olb_orbitLoop (ndt_StarHull K) hSK a.1 a.2).support, q 0 ≤ p 0) :
-- imply
  wwit_TailOdd (ndt_StarHull K) hSK a := by
-- proof
  apply StatMech.Lattice.ral_starHull_tailOdd_of_bdEdgeMatch K hSK a hmatch hqK hqfar γ

/--
[ral_unitSquare_inside_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RayAlternation.lean)
-/
@[path]
private lemma ral_unitSquare_inside_odd_eq :
-- imply
  ¬ Even (jec_rayCount (![1, 1] : Site 2) wwit_unitSquareLoop) := by
-- proof
  apply StatMech.Lattice.ral_unitSquare_inside_odd


-- created on 2026-10-23
