import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelector
open Finset StatMech StatMech.Sharpness StatMech.Sharpness.shb_DynamicEdgeExploration StatMech.Sharpness.shb_ExplorationKernel StatMech.Sharpness.shb_ExplorationRhoRealization


/--
[firstAdmissible_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelector.lean)
-/
@[path]
private lemma firstAdmissible_mem_eq
  [DecidableEq E]
  {X : shb_DynamicEdgeExploration D E}
  {admissible : D → E → Bool}
  {d : D}
  {e : E}
-- given
  (h : X.firstAdmissible admissible d = some e) :
-- imply
  e ∈ X.edgeOrder d := by
-- proof
  apply StatMech.Sharpness.shb_DynamicEdgeExploration.firstAdmissible_mem X admissible d e h

/--
[firstAdmissible_isAdmissible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelector.lean)
-/
@[path]
private lemma firstAdmissible_isAdmissible_eq
  [DecidableEq E]
  {X : shb_DynamicEdgeExploration D E}
  {admissible : D → E → Bool}
  {d : D}
  {e : E}
-- given
  (h : X.firstAdmissible admissible d = some e) :
-- imply
  admissible d e = true := by
-- proof
  apply StatMech.Sharpness.shb_DynamicEdgeExploration.firstAdmissible_isAdmissible X admissible d e h

/--
[residual_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelector.lean)
-/
@[path]
private lemma residual_nil_eq
  [DecidableEq E]
  {X : shb_DynamicEdgeExploration D E}
  {d : D} :
-- imply
  X.residual d [] = d := by
-- proof
  apply StatMech.Sharpness.shb_DynamicEdgeExploration.residual_nil X d

/--
[residual_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelector.lean)
-/
@[path]
private lemma residual_cons_eq
  [DecidableEq E]
  {X : shb_DynamicEdgeExploration D E}
  {d : D}
  {e : E}
  {es : List E} :
-- imply
  X.residual d (e :: es) = X.residual (X.advance d e) es := by
-- proof
  apply StatMech.Sharpness.shb_DynamicEdgeExploration.residual_cons X d e es

/--
[residual_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelector.lean)
-/
@[path]
private lemma residual_append_eq
  [DecidableEq E]
  {X : shb_DynamicEdgeExploration D E}
  {d : D}
  {p q : List E} :
-- imply
  X.residual d (p ++ q) = X.residual (X.residual d p) q := by
-- proof
  apply StatMech.Sharpness.shb_DynamicEdgeExploration.residual_append X d p q

/--
[determinedTrace_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelector.lean)
-/
@[path]
private lemma determinedTrace_nil_eq
  [DecidableEq E]
  {X : shb_DynamicEdgeExploration D E}
  {d : D} :
-- imply
  X.determinedTrace d [] = [] := by
-- proof
  apply StatMech.Sharpness.shb_DynamicEdgeExploration.determinedTrace_nil X d

/--
[determinedTrace_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelector.lean)
-/
@[path]
private lemma determinedTrace_cons_eq
  [DecidableEq E]
  {X : shb_DynamicEdgeExploration D E}
  {d : D}
  {e : E}
  {es : List E} :
-- imply
  X.determinedTrace d (e :: es) = X.determinedAt d e ++ X.determinedTrace (X.advance d e) es := by
-- proof
  apply StatMech.Sharpness.shb_DynamicEdgeExploration.determinedTrace_cons X d e es

/--
[determinedTrace_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelector.lean)
-/
@[path]
private lemma determinedTrace_append_eq
  [DecidableEq E]
  {X : shb_DynamicEdgeExploration D E}
  {d : D}
  {p q : List E} :
-- imply
  X.determinedTrace d (p ++ q) = X.determinedTrace d p ++ X.determinedTrace (X.residual d p) q := by
-- proof
  apply StatMech.Sharpness.shb_DynamicEdgeExploration.determinedTrace_append X d p q

/--
[selects_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelector.lean)
-/
@[path]
private lemma selects_nil_eq
  [DecidableEq E]
  {X : shb_DynamicEdgeExploration D E}
  {admissible : D → E → Bool}
  {d : D} :
-- imply
  X.Selects admissible d [] := by
-- proof
  apply StatMech.Sharpness.shb_DynamicEdgeExploration.selects_nil X admissible d

/--
[selects_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelector.lean)
-/
@[path]
private lemma selects_cons_eq
  [DecidableEq E]
  {X : shb_DynamicEdgeExploration D E}
  {admissible : D → E → Bool}
  {d : D}
  {e : E}
  {es : List E} :
-- imply
  X.Selects admissible d (e :: es) ↔ X.firstAdmissible admissible d = some e ∧ X.Selects admissible (X.advance d e) es := by
-- proof
  apply StatMech.Sharpness.shb_DynamicEdgeExploration.selects_cons X admissible d e es

/--
[selects_append_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelector.lean)
-/
@[path]
private lemma selects_append_iff_eq
  [DecidableEq E]
  {X : shb_DynamicEdgeExploration D E}
  {admissible : D → E → Bool}
  {d : D}
  {p q : List E} :
-- imply
  X.Selects admissible d (p ++ q) ↔ X.Selects admissible d p ∧ X.Selects admissible (X.residual d p) q := by
-- proof
  apply StatMech.Sharpness.shb_DynamicEdgeExploration.selects_append_iff X admissible d p q

/--
[weight_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelector.lean)
-/
@[path]
private lemma weight_nil_eq
  [Preorder D]
  [DecidableEq E]
  {K : shb_ExplorationKernel D E}
  {d : D} :
-- imply
  K.weight d [] = 1 := by
-- proof
  apply StatMech.Sharpness.shb_ExplorationKernel.weight_nil K d

/--
[weight_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelector.lean)
-/
@[path]
private lemma weight_cons_eq
  [Preorder D]
  [DecidableEq E]
  {K : shb_ExplorationKernel D E}
  {d : D}
  {e : E}
  {es : List E} :
-- imply
  K.weight d (e :: es) = K.amplitude d e * K.weight (K.exploration.advance d e) es := by
-- proof
  apply StatMech.Sharpness.shb_ExplorationKernel.weight_cons K d e es

/--
[weight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelector.lean)
-/
@[path]
private lemma weight_nonneg_eq
  [Preorder D]
  [DecidableEq E]
  {K : shb_ExplorationKernel D E}
  {d : D}
  {p : List E} :
-- imply
  0 ≤ K.weight d p := by
-- proof
  apply StatMech.Sharpness.shb_ExplorationKernel.weight_nonneg K d p

/--
[weight_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelector.lean)
-/
@[path]
private lemma weight_append_eq
  [Preorder D]
  [DecidableEq E]
  {K : shb_ExplorationKernel D E}
  {d : D}
  {p q : List E} :
-- imply
  K.weight d (p ++ q) = K.weight d p * K.weight (K.exploration.residual d p) q := by
-- proof
  apply StatMech.Sharpness.shb_ExplorationKernel.weight_append K d p q

/--
[residual_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelector.lean)
-/
@[path]
private lemma residual_mono_eq
  [Preorder D]
  [DecidableEq E]
  {K : shb_ExplorationKernel D E}
  {small large : D}
  {p : List E}
-- given
  (h : small ≤ large) :
-- imply
  K.exploration.residual small p ≤ K.exploration.residual large p := by
-- proof
  apply StatMech.Sharpness.shb_ExplorationKernel.residual_mono K h p

/--
[weight_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelector.lean)
-/
@[path]
private lemma weight_antitone_eq
  [Preorder D]
  [DecidableEq E]
  {K : shb_ExplorationKernel D E}
  {small large : D}
  {p : List E}
-- given
  (h : small ≤ large) :
-- imply
  K.weight large p ≤ K.weight small p := by
-- proof
  apply StatMech.Sharpness.shb_ExplorationKernel.weight_antitone K h p

/--
[P2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelector.lean)
-/
@[path]
private lemma P2_eq
  [Preorder D]
  [DecidableEq E]
  {R : shb_ExplorationRhoRealization D E}
  {d : D}
  {p q : List E} :
-- imply
  R.rho d (p ++ q) = R.rho d p * R.rho (R.kernel.exploration.residual d p) q := by
-- proof
  apply StatMech.Sharpness.shb_ExplorationRhoRealization.P2 R d p q

/--
[P3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelector.lean)
-/
@[path]
private lemma P3_eq
  [Preorder D]
  [DecidableEq E]
  {R : shb_ExplorationRhoRealization D E}
  {small large : D}
  {p : List E}
-- given
  (h : small ≤ large) :
-- imply
  R.rho large p ≤ R.rho small p := by
-- proof
  apply StatMech.Sharpness.shb_ExplorationRhoRealization.P3 R h p

/--
[rho_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelector.lean)
-/
@[path]
private lemma rho_nonneg_eq
  [Preorder D]
  [DecidableEq E]
  {R : shb_ExplorationRhoRealization D E}
  {d : D}
  {p : List E} :
-- imply
  0 ≤ R.rho d p := by
-- proof
  apply StatMech.Sharpness.shb_ExplorationRhoRealization.rho_nonneg R d p


-- created on 2026-10-23
