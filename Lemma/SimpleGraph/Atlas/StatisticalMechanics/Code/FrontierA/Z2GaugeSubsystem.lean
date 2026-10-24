import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.Z2GaugeSubsystem
open Finset StatMech StatMech.FrontierA


/--
[embeddingSplitEquiv_inl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeSubsystem.lean)
-/
@[path]
private lemma embeddingSplitEquiv_inl_eq
  {f : A ↪ B}
  {a : A} :
-- imply
  embeddingSplitEquiv f (.inl a) = f a := by
-- proof
  apply StatMech.FrontierA.embeddingSplitEquiv_inl f a

/--
[embeddingSplitEquiv_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeSubsystem.lean)
-/
@[path]
private lemma embeddingSplitEquiv_symm_apply_eq
  {f : A ↪ B}
  {a : A} :
-- imply
  (embeddingSplitEquiv f).symm (f a) = .inl a := by
-- proof
  apply StatMech.FrontierA.embeddingSplitEquiv_symm_apply f a

/--
[gaugeConfigSplitEquiv_apply_emb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeSubsystem.lean)
-/
@[path]
private lemma gaugeConfigSplitEquiv_apply_emb_eq
  {f : A ↪ B}
  {sigma : A → Bool}
  {a : A}
-- given
  (tau : {b : B // b ∉ Set.range f} → Bool) :
-- imply
  gaugeConfigSplitEquiv f (sigma, tau) (f a) = sigma a := by
-- proof
  apply StatMech.FrontierA.gaugeConfigSplitEquiv_apply_emb f sigma tau a

/--
[extendGaugeCoupling_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeSubsystem.lean)
-/
@[path]
private lemma extendGaugeCoupling_apply_eq
  {f : Psmall ↪ Pbig}
  {K : Psmall → Real}
  {p : Psmall} :
-- imply
  extendGaugeCoupling f K (f p) = K p := by
-- proof
  apply StatMech.FrontierA.extendGaugeCoupling_apply f K p

/--
[plaquetteSpin_gaugeConfigSplitEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeSubsystem.lean)
-/
@[path]
private lemma plaquetteSpin_gaugeConfigSplitEquiv_eq
  {incidenceSmall : Psmall → Finset Esmall}
  {incidenceBig : Pbig → Finset Ebig}
  {eEmb : Esmall ↪ Ebig}
  {pEmb : Psmall ↪ Pbig}
  {sigma : GaugeConfig Esmall}
  {p : Psmall}
-- given
  (hinc : ∀ p, incidenceBig (pEmb p) = (incidenceSmall p).map eEmb)
  (tau : {e : Ebig // e ∉ Set.range eEmb} → Bool) :
-- imply
  plaquetteSpin incidenceBig (gaugeConfigSplitEquiv eEmb (sigma, tau)) (pEmb p) = plaquetteSpin incidenceSmall sigma p := by
-- proof
  apply StatMech.FrontierA.plaquetteSpin_gaugeConfigSplitEquiv incidenceSmall incidenceBig eEmb pEmb hinc sigma tau p

/--
[gaugeAction_extendGaugeCoupling_gaugeConfigSplitEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeSubsystem.lean)
-/
@[path]
private lemma gaugeAction_extendGaugeCoupling_gaugeConfigSplitEquiv_eq
  {incidenceSmall : Psmall → Finset Esmall}
  {incidenceBig : Pbig → Finset Ebig}
  {eEmb : Esmall ↪ Ebig}
  {pEmb : Psmall ↪ Pbig}
  {K : Psmall → Real}
  {sigma : GaugeConfig Esmall}
-- given
  (hinc : ∀ p, incidenceBig (pEmb p) = (incidenceSmall p).map eEmb)
  (tau : {e : Ebig // e ∉ Set.range eEmb} → Bool) :
-- imply
  gaugeAction incidenceBig (extendGaugeCoupling pEmb K) (gaugeConfigSplitEquiv eEmb (sigma, tau)) = gaugeAction incidenceSmall K sigma := by
-- proof
  apply StatMech.FrontierA.gaugeAction_extendGaugeCoupling_gaugeConfigSplitEquiv incidenceSmall incidenceBig eEmb pEmb hinc K sigma tau

/--
[gaugeWeight_extendGaugeCoupling_gaugeConfigSplitEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeSubsystem.lean)
-/
@[path]
private lemma gaugeWeight_extendGaugeCoupling_gaugeConfigSplitEquiv_eq
  {incidenceSmall : Psmall → Finset Esmall}
  {incidenceBig : Pbig → Finset Ebig}
  {eEmb : Esmall ↪ Ebig}
  {pEmb : Psmall ↪ Pbig}
  {K : Psmall → Real}
  {sigma : GaugeConfig Esmall}
-- given
  (hinc : ∀ p, incidenceBig (pEmb p) = (incidenceSmall p).map eEmb)
  (tau : {e : Ebig // e ∉ Set.range eEmb} → Bool) :
-- imply
  gaugeWeight incidenceBig (extendGaugeCoupling pEmb K) (gaugeConfigSplitEquiv eEmb (sigma, tau)) = gaugeWeight incidenceSmall K sigma := by
-- proof
  apply StatMech.FrontierA.gaugeWeight_extendGaugeCoupling_gaugeConfigSplitEquiv incidenceSmall incidenceBig eEmb pEmb hinc K sigma tau

/--
[wilsonSpin_gaugeConfigSplitEquiv_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeSubsystem.lean)
-/
@[path]
private lemma wilsonSpin_gaugeConfigSplitEquiv_map_eq
  {eEmb : Esmall ↪ Ebig}
  {L : Finset Esmall}
  {sigma : GaugeConfig Esmall}
-- given
  (tau : {e : Ebig // e ∉ Set.range eEmb} → Bool) :
-- imply
  wilsonSpin (L.map eEmb) (gaugeConfigSplitEquiv eEmb (sigma, tau)) = wilsonSpin L sigma := by
-- proof
  apply StatMech.FrontierA.wilsonSpin_gaugeConfigSplitEquiv_map eEmb L sigma tau

/--
[gaugePartition_extendGaugeCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeSubsystem.lean)
-/
@[path]
private lemma gaugePartition_extendGaugeCoupling_eq
  {incidenceSmall : Psmall → Finset Esmall}
  {incidenceBig : Pbig → Finset Ebig}
  {eEmb : Esmall ↪ Ebig}
  {pEmb : Psmall ↪ Pbig}
  {K : Psmall → Real}
-- given
  (hinc : ∀ p, incidenceBig (pEmb p) = (incidenceSmall p).map eEmb) :
-- imply
  gaugePartition incidenceBig (extendGaugeCoupling pEmb K) = Fintype.card ({e : Ebig // e ∉ Set.range eEmb} → Bool) * gaugePartition incidenceSmall K := by
-- proof
  apply StatMech.FrontierA.gaugePartition_extendGaugeCoupling incidenceSmall incidenceBig eEmb pEmb hinc K

/--
[gaugeWilsonNumerator_extendGaugeCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeSubsystem.lean)
-/
@[path]
private lemma gaugeWilsonNumerator_extendGaugeCoupling_eq
  {incidenceSmall : Psmall → Finset Esmall}
  {incidenceBig : Pbig → Finset Ebig}
  {eEmb : Esmall ↪ Ebig}
  {pEmb : Psmall ↪ Pbig}
  {K : Psmall → Real}
  {L : Finset Esmall}
-- given
  (hinc : ∀ p, incidenceBig (pEmb p) = (incidenceSmall p).map eEmb) :
-- imply
  gaugeWilsonNumerator incidenceBig (extendGaugeCoupling pEmb K) (L.map eEmb) = Fintype.card ({e : Ebig // e ∉ Set.range eEmb} → Bool) * gaugeWilsonNumerator incidenceSmall K L := by
-- proof
  apply StatMech.FrontierA.gaugeWilsonNumerator_extendGaugeCoupling incidenceSmall incidenceBig eEmb pEmb hinc K L

/--
[gaugeWilsonExpectation_extendGaugeCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeSubsystem.lean)
-/
@[path]
private lemma gaugeWilsonExpectation_extendGaugeCoupling_eq
  {incidenceSmall : Psmall → Finset Esmall}
  {incidenceBig : Pbig → Finset Ebig}
  {eEmb : Esmall ↪ Ebig}
  {pEmb : Psmall ↪ Pbig}
  {K : Psmall → Real}
  {L : Finset Esmall}
-- given
  (hinc : ∀ p, incidenceBig (pEmb p) = (incidenceSmall p).map eEmb) :
-- imply
  gaugeWilsonExpectation incidenceBig (extendGaugeCoupling pEmb K) (L.map eEmb) = gaugeWilsonExpectation incidenceSmall K L := by
-- proof
  apply StatMech.FrontierA.gaugeWilsonExpectation_extendGaugeCoupling incidenceSmall incidenceBig eEmb pEmb hinc K L


-- created on 2026-10-23
