import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc5_core.Part2
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc5_offSupportInfinite_of_outsideInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc5_core.lean)
-/
@[path]
private lemma kc5_offSupportInfinite_of_outsideInfinite_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (h : kc4_OutsideInInfiniteComponent Vc) :
-- imply
  kc5_OutsideOffSupportInfinite Vc := by
-- proof
  apply StatMech.Walls.kc5_offSupportInfinite_of_outsideInfinite Vc h

/--
[kc5_outsideInfinite_forces_supportOdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc5_core.lean)
-/
@[path]
private lemma kc5_outsideInfinite_forces_supportOdd_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (h : kc4_OutsideInInfiniteComponent Vc) :
-- imply
  ∀ z ∈ Vc.support, ¬ Even (jec_rayCount z Vc) := by
-- proof
  apply StatMech.Walls.kc5_outsideInfinite_forces_supportOdd Vc h

/--
[kc5_outsideInfinite_iff_offSupport_and_supportOdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc5_core.lean)
-/
@[path]
private lemma kc5_outsideInfinite_iff_offSupport_and_supportOdd_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  kc4_OutsideInInfiniteComponent Vc ↔ (kc5_OutsideOffSupportInfinite Vc ∧ ∀ z ∈ Vc.support, ¬ Even (jec_rayCount z Vc)) := by
-- proof
  apply StatMech.Walls.kc5_outsideInfinite_iff_offSupport_and_supportOdd Vc

/--
[kc5_offSupportReaches_of_corrected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc5_core.lean)
-/
@[path]
private lemma kc5_offSupportReaches_of_corrected_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (h : kc5_OutsideOffSupportInfinite Vc) :
-- imply
  kc5_OffSupportReachesExterior Vc R := by
-- proof
  apply StatMech.Walls.kc5_offSupportReaches_of_corrected Vc R hsupp h

/--
[kc5_corrected_seed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc5_core.lean)
-/
@[path]
private lemma kc5_corrected_seed_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R)
  (hz : z ∈ exterior 2 R) :
-- imply
  z ∉ Vc.support ∧ z ∉ jec_leftRegion Vc ∧ ∃ hzmem : z ∈ (oc_supportSet Vc)ᶜ, (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk ⟨z, hzmem⟩).supp.Infinite := by
-- proof
  apply StatMech.Walls.kc5_corrected_seed Vc R hsupp hz

/--
[kc5_corrected_conclusion_seed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc5_core.lean)
-/
@[path]
private lemma kc5_corrected_conclusion_seed_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R)
  (hz : z ∈ exterior 2 R) :
-- imply
  ∃ hzmem : z ∈ (oc_supportSet Vc)ᶜ, (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk ⟨z, hzmem⟩).supp.Infinite := by
-- proof
  apply StatMech.Walls.kc5_corrected_conclusion_seed Vc R hsupp hz


-- created on 2026-10-23
