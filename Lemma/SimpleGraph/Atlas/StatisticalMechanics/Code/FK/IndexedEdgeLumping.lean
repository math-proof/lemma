import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.IndexedEdgeLumping
open Finset StatMech StatMech.FK


/--
[sum_indexedBernoulliWeight_bundleSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IndexedEdgeLumping.lean)
-/
@[path]
private lemma sum_indexedBernoulliWeight_bundleSupport_eq
  [Fintype E]
  [DecidableEq E]
  {p : Real}
  {f : E → A}
  {F : (A → Bool) → Real} :
-- imply
  ∑ eta : E → Bool, indexedBernoulliWeight p eta * F (indexedBundleSupport f eta) = ∑ rho : A → Bool, (∏ a, if rho a then indexedEffectiveParam f p a else 1 - indexedEffectiveParam f p a) * F rho := by
-- proof
  apply StatMech.FK.sum_indexedBernoulliWeight_bundleSupport p f F

/--
[sum_indexedBernoulliWeight_restrictActive_bundleSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IndexedEdgeLumping.lean)
-/
@[path]
private lemma sum_indexedBernoulliWeight_restrictActive_bundleSupport_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : Real}
  {f : E → Sym2 V}
  {F : ConfigSpace G.edgeSet → Real} :
-- imply
  ∑ eta : E → Bool, indexedBernoulliWeight p eta * F (restrictActive G (indexedBundleSupport f eta)) = ∑ rho : ConfigSpace G.edgeSet, (∏ a, if rho a then indexedEffectiveParam f p a.1 else 1 - indexedEffectiveParam f p a.1) * F rho := by
-- proof
  apply StatMech.FK.sum_indexedBernoulliWeight_restrictActive_bundleSupport G p f F


-- created on 2026-10-23
