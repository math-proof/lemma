import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.FreeEvenHomogeneity.Part3
open MeasureTheory Filter Topology StatMech StatMech.FrontierB


/--
[freeDomainSpinSupport_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenHomogeneity.lean)
-/
@[path]
private lemma freeDomainSpinSupport_image_eq
  {d : Nat}
  {K A : Finset (Site d)}
-- given
  (hA : A ⊆ K) :
-- imply
  (freeDomainSpinSupport K A).image Subtype.val = A := by
-- proof
  apply StatMech.FrontierB.freeDomainSpinSupport_image K A hA

/--
[freeDomainInclusionEquiv_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenHomogeneity.lean)
-/
@[path]
private lemma freeDomainInclusionEquiv_adj_eq
  {d : Nat}
  {K L : Finset (Site d)}
  {x y : freeDomainVertices K}
-- given
  (hKL : K ⊆ L) :
-- imply
  (freeDomainGraph K).Adj x y ↔ ((freeDomainGraph L).comap (Subtype.val : {z : freeDomainVertices L // z.1 ∈ K} -> freeDomainVertices L)).Adj (freeDomainInclusionEquiv hKL x) (freeDomainInclusionEquiv hKL y) := by
-- proof
  apply StatMech.FrontierB.freeDomainInclusionEquiv_adj hKL x y

/--
[freeDomainSpinSupport_map_inclusion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenHomogeneity.lean)
-/
@[path]
private lemma freeDomainSpinSupport_map_inclusion_eq
  {d : Nat}
  {K L : Finset (Site d)}
  {A : Finset (Site d)}
-- given
  (hKL : K ⊆ L)
  (hA : A ⊆ K) :
-- imply
  ((freeDomainSpinSupport K A).map (freeDomainInclusionEquiv hKL).toEmbedding).map (Function.Embedding.subtype (fun z : freeDomainVertices L => z.1 ∈ K)) = freeDomainSpinSupport L A := by
-- proof
  apply StatMech.FrontierB.freeDomainSpinSupport_map_inclusion hKL A hA

/--
[freeDomain_spinProd_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenHomogeneity.lean)
-/
@[path]
private lemma freeDomain_spinProd_mono_eq
  {d : Nat}
  {K L : Finset (Site d)}
  {beta : Real}
  {A : Finset (Site d)}
-- given
  (hKL : K ⊆ L)
  (hbeta : 0 <= beta)
  (hA : A ⊆ K) :
-- imply
  isingExpectation (freeDomainGraph K) beta 0 (spinProd (freeDomainSpinSupport K A)) <= isingExpectation (freeDomainGraph L) beta 0 (spinProd (freeDomainSpinSupport L A)) := by
-- proof
  apply StatMech.FrontierB.freeDomain_spinProd_mono hKL beta hbeta A hA

/--
[freeDomainTranslateEquiv_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenHomogeneity.lean)
-/
@[path]
private lemma freeDomainTranslateEquiv_adj_eq
  {d : Nat}
  {g : Multiplicative (Site d)}
  {K : Finset (Site d)}
  {x y : freeDomainVertices K} :
-- imply
  (freeDomainGraph K).Adj x y ↔ (freeDomainGraph (K.image fun z => g • z)).Adj (freeDomainTranslateEquiv g K x) (freeDomainTranslateEquiv g K y) := by
-- proof
  apply StatMech.FrontierB.freeDomainTranslateEquiv_adj g K x y

/--
[freeDomainSpinSupport_map_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenHomogeneity.lean)
-/
@[path]
private lemma freeDomainSpinSupport_map_translate_eq
  {d : Nat}
  {g : Multiplicative (Site d)}
  {K A : Finset (Site d)} :
-- imply
  (freeDomainSpinSupport K A).map (freeDomainTranslateEquiv g K).toEmbedding = freeDomainSpinSupport (K.image fun x => g • x) (A.image fun x => g • x) := by
-- proof
  apply StatMech.FrontierB.freeDomainSpinSupport_map_translate g K A

/--
[freeDomain_spinProd_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenHomogeneity.lean)
-/
@[path]
private lemma freeDomain_spinProd_translate_eq
  {d : Nat}
  {g : Multiplicative (Site d)}
  {K A : Finset (Site d)}
  {beta : Real} :
-- imply
  isingExpectation (freeDomainGraph (K.image fun x => g • x)) beta 0 (spinProd (freeDomainSpinSupport (K.image fun x => g • x) (A.image fun x => g • x))) = isingExpectation (freeDomainGraph K) beta 0 (spinProd (freeDomainSpinSupport K A)) := by
-- proof
  apply StatMech.FrontierB.freeDomain_spinProd_translate g K A beta

/--
[freeDomainGraph_box_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenHomogeneity.lean)
-/
@[path]
private lemma freeDomainGraph_box_relabel_eq
  {d n : Nat}
  {beta : Real}
  {A : Finset (Site d)} :
-- imply
  isingExpectation (freeDomainGraph (boxFinset d n)) beta 0 (spinProd (freeDomainSpinSupport (boxFinset d n) A)) = isingExpectation (sctBoxGraph d n) beta 0 (spinProd (boxSpinSupport d n A)) := by
-- proof
  apply StatMech.FrontierB.freeDomainGraph_box_relabel d n beta A

/--
[integral_freeMeasure_spinProd_eq_freeDomain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenHomogeneity.lean)
-/
@[path]
private lemma integral_freeMeasure_spinProd_eq_freeDomain_eq
  {d n : Nat}
  {beta : Real}
  {A : Finset (Site d)}
-- given
  (hA : A ⊆ boxFinset d n) :
-- imply
  (∫ omega, spinProd A omega ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) = isingExpectation (freeDomainGraph (boxFinset d n)) beta 0 (spinProd (freeDomainSpinSupport (boxFinset d n) A)) := by
-- proof
  apply StatMech.FrontierB.integral_freeMeasure_spinProd_eq_freeDomain d n beta A hA

/--
[integral_freeState_spinProd_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenHomogeneity.lean)
-/
@[path]
private lemma integral_freeState_spinProd_translate_eq
  {d : Nat}
  {beta : Real}
  {g : Multiplicative (Site d)}
  {A : Finset (Site d)}
-- given
  (hbeta : 0 <= beta) :
-- imply
  (∫ omega, spinProd (A.image fun x => g • x) omega ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) = ∫ omega, spinProd A omega ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierB.integral_freeState_spinProd_translate d beta hbeta g A

/--
[spinProd_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenHomogeneity.lean)
-/
@[path]
private lemma spinProd_shift_eq
  {d : Nat}
  {g : Multiplicative (Site d)}
  {A : Finset (Site d)}
  {omega : ConfigSpace (Site d)} :
-- imply
  spinProd A (ConfigSpace.shift g omega) = spinProd (A.image fun x => g⁻¹ • x) omega := by
-- proof
  apply StatMech.FrontierB.spinProd_shift g A omega

/--
[fmu_moInd_eq_spinProd_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenHomogeneity.lean)
-/
@[path]
private lemma fmu_moInd_eq_spinProd_sum_eq
  {d : Nat}
  {T : Finset (Site d)}
  {omega : ConfigSpace (Site d)} :
-- imply
  StatMech.FK.fmu_moInd T omega = (1 / 2 : Real) ^ T.card * ∑ U ∈ T.powerset, spinProd U omega := by
-- proof
  apply StatMech.FrontierB.fmu_moInd_eq_spinProd_sum T omega

/--
[integral_freeState_moInd_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenHomogeneity.lean)
-/
@[path]
private lemma integral_freeState_moInd_shift_eq
  {d : Nat}
  {beta : Real}
  {g : Multiplicative (Site d)}
  {T : Finset (Site d)}
-- given
  (hbeta : 0 <= beta) :
-- imply
  (∫ omega, StatMech.FK.fmu_moInd T (ConfigSpace.shift g omega) ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) = ∫ omega, StatMech.FK.fmu_moInd T omega ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierB.integral_freeState_moInd_shift d beta hbeta g T

/--
[freeState_multiOpen_preimage_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenHomogeneity.lean)
-/
@[path]
private lemma freeState_multiOpen_preimage_eq_eq
  {d : Nat}
  {beta : Real}
  {g : Multiplicative (Site d)}
  {T : Finset (Site d)}
-- given
  (hbeta : 0 <= beta) :
-- imply
  (freeState d beta 0 : Measure (ConfigSpace (Site d))).real ((ConfigSpace.shift g) ⁻¹' StatMech.FK.fmu_multiOpen T) = (freeState d beta 0 : Measure (ConfigSpace (Site d))).real (StatMech.FK.fmu_multiOpen T) := by
-- proof
  apply StatMech.FrontierB.freeState_multiOpen_preimage_eq d beta hbeta g T

/--
[freeState_isTranslationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenHomogeneity.lean)
-/
@[path]
private lemma freeState_isTranslationInvariant_eq
  {d : Nat}
  {beta : Real}
-- given
  (hbeta : 0 <= beta) :
-- imply
  ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (freeState d beta 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierB.freeState_isTranslationInvariant d beta hbeta


-- created on 2026-10-23
