import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc3_evenoddrule
open Set SimpleGraph Function StatMech.Lattice StatMech StatMech.Walls


/--
[kc3_eor_farLeft_rayCount_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_evenoddrule.lean)
-/
@[path]
private lemma kc3_eor_farLeft_rayCount_zero_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {t : Site 2}
-- given
  (ht : ∀ p ∈ Vc.support, t 0 ≤ p 0) :
-- imply
  jec_rayCount t Vc = 0 := by
-- proof
  apply StatMech.Walls.kc3_eor_farLeft_rayCount_zero Vc t ht

/--
[kc3_eor_farLeft_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_evenoddrule.lean)
-/
@[path]
private lemma kc3_eor_farLeft_even_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {t : Site 2}
-- given
  (ht : ∀ p ∈ Vc.support, t 0 ≤ p 0) :
-- imply
  Even (jec_rayCount t Vc) := by
-- proof
  apply StatMech.Walls.kc3_eor_farLeft_even Vc t ht

/--
[kc3_eor_farLeft_notMem_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_evenoddrule.lean)
-/
@[path]
private lemma kc3_eor_farLeft_notMem_leftRegion_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {t : Site 2}
-- given
  (ht : ∀ p ∈ Vc.support, t 0 ≤ p 0) :
-- imply
  t ∉ jec_leftRegion Vc := by
-- proof
  apply StatMech.Walls.kc3_eor_farLeft_notMem_leftRegion Vc t ht

/--
[kc3_evenOddRule](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_evenoddrule.lean)
-/
@[path]
private lemma kc3_evenOddRule_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z t : Site 2}
  {γ : (hypercubicLattice 2).Walk z t}
-- given
  (ht : ∀ p ∈ Vc.support, t 0 ≤ p 0) :
-- imply
  (¬ Even (jec_rayCount z Vc)) ↔ (¬ Even (crossCount (jec_leftRegion Vc) γ)) := by
-- proof
  apply StatMech.Walls.kc3_evenOddRule Vc ht γ

/--
[kc3_evenOddRule_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_evenoddrule.lean)
-/
@[path]
private lemma kc3_evenOddRule_even_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z t : Site 2}
  {γ : (hypercubicLattice 2).Walk z t}
-- given
  (ht : ∀ p ∈ Vc.support, t 0 ≤ p 0) :
-- imply
  Even (jec_rayCount z Vc) ↔ Even (crossCount (jec_leftRegion Vc) γ) := by
-- proof
  apply StatMech.Walls.kc3_evenOddRule_even Vc ht γ

/--
[kc3_evenOddRule_mod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_evenoddrule.lean)
-/
@[path]
private lemma kc3_evenOddRule_mod_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z t : Site 2}
  {γ : (hypercubicLattice 2).Walk z t}
-- given
  (ht : ∀ p ∈ Vc.support, t 0 ≤ p 0) :
-- imply
  jec_rayCount z Vc % 2 = crossCount (jec_leftRegion Vc) γ % 2 := by
-- proof
  apply StatMech.Walls.kc3_evenOddRule_mod Vc ht γ

/--
[kc3_memLeftRegion_iff_oddCross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_evenoddrule.lean)
-/
@[path]
private lemma kc3_memLeftRegion_iff_oddCross_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z t : Site 2}
  {γ : (hypercubicLattice 2).Walk z t}
-- given
  (ht : ∀ p ∈ Vc.support, t 0 ≤ p 0) :
-- imply
  z ∈ jec_leftRegion Vc ↔ ¬ Even (crossCount (jec_leftRegion Vc) γ) := by
-- proof
  apply StatMech.Walls.kc3_memLeftRegion_iff_oddCross Vc ht γ

/--
[kc3_crossCount_indep_of_escape](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_evenoddrule.lean)
-/
@[path]
private lemma kc3_crossCount_indep_of_escape_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z t₁ t₂ : Site 2}
  {γ₁ : (hypercubicLattice 2).Walk z t₁}
  {γ₂ : (hypercubicLattice 2).Walk z t₂}
-- given
  (ht₁ : ∀ p ∈ Vc.support, t₁ 0 ≤ p 0)
  (ht₂ : ∀ p ∈ Vc.support, t₂ 0 ≤ p 0) :
-- imply
  crossCount (jec_leftRegion Vc) γ₁ % 2 = crossCount (jec_leftRegion Vc) γ₂ % 2 := by
-- proof
  apply StatMech.Walls.kc3_crossCount_indep_of_escape Vc ht₁ ht₂ γ₁ γ₂

/--
[kc3_evenOddRule_node](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_evenoddrule.lean)
-/
@[path]
private lemma kc3_evenOddRule_node_eq :
-- imply
  (∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a) (z t : Site 2), (∀ p ∈ Vc.support, t 0 ≤ p 0) → ∀ γ : (hypercubicLattice 2).Walk z t, (¬ Even (jec_rayCount z Vc)) ↔ (¬ Even (crossCount (jec_leftRegion Vc) γ))) ∧ (∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a) (t : Site 2), (∀ p ∈ Vc.support, t 0 ≤ p 0) → t ∉ jec_leftRegion Vc) := by
-- proof
  apply StatMech.Walls.kc3_evenOddRule_node


-- created on 2026-10-23
