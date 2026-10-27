import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.PlusEvenMixing.Part2
open MeasureTheory Set StatMech StatMech.FrontierB


/--
[siteTranslation_solution_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusEvenMixing.lean)
-/
@[path]
private lemma siteTranslation_solution_finite_eq
  {d : Nat}
  {x y : Site d} :
-- imply
  {g : Multiplicative (Site d) | g • x = y}.Finite := by
-- proof
  apply StatMech.FrontierB.siteTranslation_solution_finite x y

/--
[mem_edgeVertexSupport_of_mem_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusEvenMixing.lean)
-/
@[path]
private lemma mem_edgeVertexSupport_of_mem_edge_eq
  {d : Nat}
  {F : Finset (Sym2 (Site d))}
  {e : Sym2 (Site d)}
  {x : Site d}
-- given
  (he : e ∈ F)
  (hx : x ∈ e) :
-- imply
  x ∈ edgeVertexSupport F := by
-- proof
  apply StatMech.FrontierB.mem_edgeVertexSupport_of_mem_edge he hx

/--
[iti_monomialBcf_eq_fmu_moInd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusEvenMixing.lean)
-/
@[path]
private lemma iti_monomialBcf_eq_fmu_moInd_eq
  {d : Nat}
  {T : Finset (Site d)}
  {omega : ConfigSpace (Site d)} :
-- imply
  iti_monomialBcf T omega = fmu_moInd T omega := by
-- proof
  apply StatMech.FrontierB.iti_monomialBcf_eq_fmu_moInd T omega

/--
[exp_neg_edgeSpinSum_eq_plusEvenExpansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusEvenMixing.lean)
-/
@[path]
private lemma exp_neg_edgeSpinSum_eq_plusEvenExpansion_eq
  {d : Nat}
  {beta : Real}
  {F : Finset (Sym2 (Site d))}
  {omega : ConfigSpace (Site d)}
-- given
  (hF : ∀ e ∈ F, ¬ e.IsDiag) :
-- imply
  Real.exp (-beta * edgeSpinSum F omega) = ∑ i ∈ plusEvenExpansionIndices F, plusEvenExpansionCoeff beta F i * fmu_moInd (plusEvenExpansionSupport i) omega := by
-- proof
  apply StatMech.FrontierB.exp_neg_edgeSpinSum_eq_plusEvenExpansion beta F hF omega

/--
[integral_exp_neg_edgeSpinSum_eq_plusEvenExpansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusEvenMixing.lean)
-/
@[path]
private lemma integral_exp_neg_edgeSpinSum_eq_plusEvenExpansion_eq
  {d : Nat}
  {mu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure mu]
  {beta : Real}
  {F : Finset (Sym2 (Site d))}
-- given
  (hF : ∀ e ∈ F, ¬ e.IsDiag) :
-- imply
  (∫ omega, Real.exp (-beta * edgeSpinSum F omega) ∂mu) = ∑ i ∈ plusEvenExpansionIndices F, plusEvenExpansionCoeff beta F i * mu.real (fmu_multiOpen (plusEvenExpansionSupport i)) := by
-- proof
  apply StatMech.FrontierB.integral_exp_neg_edgeSpinSum_eq_plusEvenExpansion mu beta F hF

/--
[plusState_deletedEdge_pairMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusEvenMixing.lean)
-/
@[path]
private lemma plusState_deletedEdge_pairMixing_eq
  {d : Nat}
  {beta : Real}
  {F F' : Finset (Sym2 (Site d))}
  {epsilon : Real}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 ≤ beta)
  (hF : ∀ e ∈ F, ¬ e.IsDiag)
  (hF' : ∀ e ∈ F', ¬ e.IsDiag)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ g : Multiplicative (Site d), Disjoint F (currentShiftFinset g F') ∧ abs ((∫ omega, Real.exp (-beta * edgeSpinSum F omega) * Real.exp (-beta * edgeSpinSum F' (shift g omega)) ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) - (∫ omega, Real.exp (-beta * edgeSpinSum F omega) ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) * (∫ omega, Real.exp (-beta * edgeSpinSum F' omega) ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))))) < epsilon := by
-- proof
  apply StatMech.FrontierB.plusState_deletedEdge_pairMixing hd hbeta F F' hF hF' epsilon hepsilon

/--
[currentParityAvoidCylinder_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusEvenMixing.lean)
-/
@[path]
private lemma currentParityAvoidCylinder_inter_eq
  [DecidableEq E]
  {F F' : Finset E} :
-- imply
  currentParityAvoidCylinder F ∩ currentParityAvoidCylinder F' = currentParityAvoidCylinder (F ∪ F') := by
-- proof
  apply StatMech.FrontierB.currentParityAvoidCylinder_inter F F'

/--
[edgeSpinSum_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusEvenMixing.lean)
-/
@[path]
private lemma edgeSpinSum_union_eq
  {d : Nat}
  {F F' : Finset (Sym2 (Site d))}
  {omega : ConfigSpace (Site d)}
-- given
  (hdisj : Disjoint F F') :
-- imply
  edgeSpinSum (F ∪ F') omega = edgeSpinSum F omega + edgeSpinSum F' omega := by
-- proof
  apply StatMech.FrontierB.edgeSpinSum_union hdisj omega

/--
[infinitePlusCurrentMeasure_parityAvoid_real_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusEvenMixing.lean)
-/
@[path]
private lemma infinitePlusCurrentMeasure_parityAvoid_real_eq_eq
  {d : Nat}
  {beta : Real}
  {F : Finset (Sym2 (Site d))}
-- given
  (hbeta : 0 < beta)
  (hF : (↑F : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet) :
-- imply
  (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real (currentParityAvoidCylinder F) = (∫ omega, Real.exp (-beta * edgeSpinSum F omega) ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) * Real.cosh beta ^ F.card := by
-- proof
  apply StatMech.FrontierB.infinitePlusCurrentMeasure_parityAvoid_real_eq hbeta F hF

/--
[infinitePlusCurrentMeasure_parityAvoid_inter_shift_real_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusEvenMixing.lean)
-/
@[path]
private lemma infinitePlusCurrentMeasure_parityAvoid_inter_shift_real_eq_eq
  {d : Nat}
  {beta : Real}
  {g : Multiplicative (Site d)}
  {F F' : Finset (Sym2 (Site d))}
-- given
  (hbeta : 0 < beta)
  (hF : (↑F : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (hF' : (↑F' : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (hdisj : Disjoint F (currentShiftFinset g F')) :
-- imply
  (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real (currentParityAvoidCylinder F ∩ (currentShift g) ⁻¹' currentParityAvoidCylinder F') = (∫ omega, Real.exp (-beta * edgeSpinSum F omega) * Real.exp (-beta * edgeSpinSum F' (shift g omega)) ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) * (Real.cosh beta ^ F.card * Real.cosh beta ^ F'.card) := by
-- proof
  apply StatMech.FrontierB.infinitePlusCurrentMeasure_parityAvoid_inter_shift_real_eq hbeta g F F' hF hF' hdisj

/--
[infinitePlusCurrentMeasure_parityAvoid_pairMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusEvenMixing.lean)
-/
@[path]
private lemma infinitePlusCurrentMeasure_parityAvoid_pairMixing_eq
  {d : Nat}
  {beta : Real}
  {F F' : Finset (Sym2 (Site d))}
  {epsilon : Real}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hF : (↑F : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (hF' : (↑F' : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ g : Multiplicative (Site d), Disjoint F (currentShiftFinset g F') ∧ abs ((infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real (currentParityAvoidCylinder F ∩ (currentShift g) ⁻¹' currentParityAvoidCylinder F') - (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real (currentParityAvoidCylinder F) * (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real (currentParityAvoidCylinder F')) < epsilon := by
-- proof
  apply StatMech.FrontierB.infinitePlusCurrentMeasure_parityAvoid_pairMixing hd hbeta F F' hF hF' epsilon hepsilon


-- created on 2026-10-23
