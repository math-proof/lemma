import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.DisjointGraphFactorizeClose
open MeasureTheory Filter Topology Set SimpleGraph StatMech.ConfigSpace StatMech.Lattice StatMech StatMech.FK


/--
[dgf_disjoint_product_dom_doubleCap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DisjointGraphFactorizeClose.lean)
-/
@[path]
private lemma dgf_disjoint_product_dom_doubleCap_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G C : SimpleGraph V}
  {p q : ℝ}
  {F : Finset (Sym2 V)}
  {C' : SimpleGraph V}
  [DecidableRel C'.Adj]
  {A B : Set (ConfigSpace (Sym2 V))}
  {α β : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hCC' : C ≤ C')
  (hA : IsIncreasing A)
  (hB : DependsOnOutside F B)
  (hα : 0 ≤ α)
  (hAcap : ∀ ψ ∈ fibreReps F, (∑ ρ, A.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C' p q F ψ ρ) ≤ α)
  (hBcap : (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * bcProb G C p q ρ) ≤ β) :
-- imply
  (∑ ρ, (A ∩ B).indicator (fun _ => (1:ℝ)) ρ * bcProb G C p q ρ) ≤ α * β := by
-- proof
  apply StatMech.FK.dgf_disjoint_product_dom_doubleCap G C hp hp1 hq C' hCC' hA hB hα hAcap hBcap

/--
[dgf_boxMultiOpen_dependsOnOutside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DisjointGraphFactorizeClose.lean)
-/
@[path]
private lemma dgf_boxMultiOpen_dependsOnOutside_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G C : SimpleGraph V}
  {M : ℕ}
  {F : Finset (Sym2 (boxVerts d M))}
  {t : Finset (Sym2 (boxVerts d M))}
-- given
  (hdisj : ∀ e ∈ t, e ∉ F) :
-- imply
  DependsOnOutside F (cdc_boxMultiOpenEvent M t) := by
-- proof
  apply StatMech.FK.dgf_boxMultiOpen_dependsOnOutside G C M F t hdisj

/--
[dgf_cross_eq_boxRestrict_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DisjointGraphFactorizeClose.lean)
-/
@[path]
private lemma dgf_cross_eq_boxRestrict_inter_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G C : SimpleGraph V}
  {M : ℕ}
  {g : Multiplicative (Site d)}
  {T T' : Finset (Sym2 (Site d))}
  {tT tT' : Finset (Sym2 (boxVerts d M))}
-- given
  (hT : T = tT.image (edgeIncl d M))
  (hT' : T'.image (fun e => g⁻¹ • e) = tT'.image (edgeIncl d M)) :
-- imply
  (fmu_multiOpen T ∩ (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) ⁻¹' fmu_multiOpen T') = boxRestrict d M ⁻¹' (cdc_boxMultiOpenEvent M tT ∩ cdc_boxMultiOpenEvent M tT') := by
-- proof
  apply StatMech.FK.dgf_cross_eq_boxRestrict_inter G C M g T T' tT tT' hT hT'

/--
[dgf_factorise_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DisjointGraphFactorizeClose.lean)
-/
@[path]
private lemma dgf_factorise_pair_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G C : SimpleGraph V}
  {p : ℝ}
  {N r : ℕ}
  {g : Multiplicative (Site d)}
  {T T' : Finset (Sym2 (Site d))}
  {F tT tT' : Finset (Sym2 (boxVerts d (N + r)))}
  {C' : SimpleGraph (boxVerts d (N + r))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hC'dec : DecidableRel C'.Adj)
  (hT : T = tT.image (edgeIncl d (N + r)))
  (hT' : T'.image (fun e => g⁻¹ • e) = tT'.image (edgeIncl d (N + r)))
  (hdisj : ∀ e ∈ tT', e ∉ F)
  (hCC' : boundaryCliqueGraph (boxBoundary d (N + r)) ≤ C')
  (hαcap : ∀ ψ ∈ fibreReps F, (∑ ρ, (cdc_boxMultiOpenEvent (N + r) tT).indicator (fun _ => (1:ℝ)) ρ * condBcProb (boxGraph d (N + r)) C' p 2 F ψ ρ) ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T))
  (hBcap : (wiredFiniteMeasure d (N + r) hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d (N + r) ⁻¹' (cdc_boxMultiOpenEvent (N + r) tT')) ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')) :
-- imply
  (wiredFiniteMeasure d (N + r) hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T ∩ (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) ⁻¹' fmu_multiOpen T') ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T) * (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T') := by
-- proof
  apply StatMech.FK.dgf_factorise_pair G C hp hp1 hC'dec hT hT' hdisj hCC' hαcap hBcap

/--
[dgf_cross_support_realised](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DisjointGraphFactorizeClose.lean)
-/
@[path]
private lemma dgf_cross_support_realised_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G C : SimpleGraph V}
  {M : ℕ}
  {g : Multiplicative (Site d)}
  {T T' : Finset (Sym2 (Site d))}
  {tT tT' : Finset (Sym2 (boxVerts d M))}
-- given
  (hT : T = tT.image (edgeIncl d M))
  (hT' : T'.image (fun e => g⁻¹ • e) = tT'.image (edgeIncl d M)) :
-- imply
  T ∪ T'.image (fun e => g⁻¹ • e) = (tT ∪ tT').image (edgeIncl d M) := by
-- proof
  apply StatMech.FK.dgf_cross_support_realised G C hT hT'

/--
[dgf_wiredDisjointBoxFactorise_of_conditionalCap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DisjointGraphFactorizeClose.lean)
-/
@[path]
private lemma dgf_wiredDisjointBoxFactorise_of_conditionalCap_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G C : SimpleGraph V}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hcap : dgf_DisjointBoxAnalyticCap (d := d) hp hp1) :
-- imply
  fwm_WiredDisjointBoxFactorise hp hp1 (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))) := by
-- proof
  apply StatMech.FK.dgf_wiredDisjointBoxFactorise_of_conditionalCap G C hp hp1 hcap

/--
[dgf_disjointBoxAnalyticCap_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DisjointGraphFactorizeClose.lean)
-/
@[path]
private lemma dgf_disjointBoxAnalyticCap_nonvacuous_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G C : SimpleGraph V}
  {p : ℝ}
  {N : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  ∃ (g : Multiplicative (Site d)) (r : ℕ), ∃ (F tT tT' : Finset (Sym2 (boxVerts d (N + r)))) (C' : SimpleGraph (boxVerts d (N + r))) (_ : DecidableRel C'.Adj), (∅ : Finset (Sym2 (Site d))) = tT.image (edgeIncl d (N + r)) ∧ (∅ : Finset (Sym2 (Site d))).image (fun e => (1 : Multiplicative (Site d))⁻¹ • e) = tT'.image (edgeIncl d (N + r)) ∧ (∀ e ∈ tT', e ∉ F) ∧ boundaryCliqueGraph (boxBoundary d (N + r)) ≤ C' ∧ (∀ ψ ∈ fibreReps F, (∑ ρ, (cdc_boxMultiOpenEvent (N + r) tT).indicator (fun _ => (1:ℝ)) ρ * condBcProb (boxGraph d (N + r)) C' p 2 F ψ ρ) ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen (∅ : Finset (Sym2 (Site d))))) ∧ ((wiredFiniteMeasure d (N + r) hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d (N + r) ⁻¹' (cdc_boxMultiOpenEvent (N + r) tT')) ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen (∅ : Finset (Sym2 (Site d))))) := by
-- proof
  apply StatMech.FK.dgf_disjointBoxAnalyticCap_nonvacuous G C hp hp1 N

/--
[dgf_wiredIV_isErgodic_of_conditionalCap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DisjointGraphFactorizeClose.lean)
-/
@[path]
private lemma dgf_wiredIV_isErgodic_of_conditionalCap_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G C : SimpleGraph V}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hcap : dgf_DisjointBoxAnalyticCap (d := d) hp hp1) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.dgf_wiredIV_isErgodic_of_conditionalCap G C hp hp1 hcap


-- created on 2026-10-23
