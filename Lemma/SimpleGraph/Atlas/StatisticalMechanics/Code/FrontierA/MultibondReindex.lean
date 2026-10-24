import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.MultibondReindex
open Finset StatMech StatMech.FrontierA


/--
[multibondIsingWeight_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MultibondReindex.lean)
-/
@[path]
private lemma multibondIsingWeight_reindex_eq
  {eP : P ≃ P'}
  {eV : V ≃ V'}
-- given
  (ends : P -> V × V)
  (ends' : P' -> V' × V')
  (J : P -> Real)
  (J' : P' -> Real)
  (hJ : forall p, J' (eP p) = J p)
  (hagrees : forall p s, (multibondConfigReindex eV s) (ends' (eP p)).1 = (multibondConfigReindex eV s) (ends' (eP p)).2 <-> s (ends p).1 = s (ends p).2)
  (s : V -> Bool) :
-- imply
  multibondIsingWeight ends' J' (multibondConfigReindex eV s) = multibondIsingWeight ends J s := by
-- proof
  apply StatMech.FrontierA.multibondIsingWeight_reindex eP eV ends ends' J J' hJ hagrees s

/--
[multibondIsingPartition_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MultibondReindex.lean)
-/
@[path]
private lemma multibondIsingPartition_reindex_eq
  {eP : P ≃ P'}
  {eV : V ≃ V'}
-- given
  (ends : P -> V × V)
  (ends' : P' -> V' × V')
  (J : P -> Real)
  (J' : P' -> Real)
  (hJ : forall p, J' (eP p) = J p)
  (hagrees : forall p s, (multibondConfigReindex eV s) (ends' (eP p)).1 = (multibondConfigReindex eV s) (ends' (eP p)).2 <-> s (ends p).1 = s (ends p).2) :
-- imply
  multibondIsingPartition ends' J' = multibondIsingPartition ends J := by
-- proof
  apply StatMech.FrontierA.multibondIsingPartition_reindex eP eV ends ends' J J' hJ hagrees

/--
[multibondDisorderFreeEnergy_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MultibondReindex.lean)
-/
@[path]
private lemma multibondDisorderFreeEnergy_reindex_eq
  {eP : P ≃ P'}
  {eV : V ≃ V'}
  {D : Finset P}
-- given
  (ends : P -> V × V)
  (ends' : P' -> V' × V')
  (J : P -> Real)
  (J' : P' -> Real)
  (hJ : forall p, J' (eP p) = J p)
  (hagrees : forall p s, (multibondConfigReindex eV s) (ends' (eP p)).1 = (multibondConfigReindex eV s) (ends' (eP p)).2 <-> s (ends p).1 = s (ends p).2) :
-- imply
  multibondDisorderFreeEnergy ends' J' (D.map eP.toEmbedding) = multibondDisorderFreeEnergy ends J D := by
-- proof
  apply StatMech.FrontierA.multibondDisorderFreeEnergy_reindex eP eV ends ends' J J' D hJ hagrees


-- created on 2026-10-23
