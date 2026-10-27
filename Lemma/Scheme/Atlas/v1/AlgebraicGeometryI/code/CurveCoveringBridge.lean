import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.CurveCoveringBridge
open RiemannHurwitzFormula CanonicalSheafCurves RiemannHurwitzDegree


/--
[CurveCovering.toCurveMorphismData_satisfies_RH](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CurveCoveringBridge.lean)
-/
@[path]
lemma CurveCovering.toCurveMorphismData_satisfies_RH
  {C : CurveCovering} :
-- imply
  C.toCurveMorphismData.deg_KX = C.toCurveMorphismData.degree * C.toCurveMorphismData.deg_KY + C.toCurveMorphismData.deg_R := by
-- proof
  show C.X.degK = C.n * C.Y.degK + C.deg_R
  exact C.degK_eq

/--
[CurveCovering.ellipticIdentity_morphismData](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CurveCoveringBridge.lean)
-/
@[path]
lemma CurveCovering.ellipticIdentity_morphismData
-- imply
  CurveCovering.ellipticIdentity.toCurveMorphismData.degree = 1 ∧ CurveCovering.ellipticIdentity.toCurveMorphismData.deg_R = 0 :=
-- proof
⟨rfl, CurveCovering.ellipticIdentity_deg_R⟩

/--
[CurveCovering.ellipticIdentity_toCurveMorphismData_RH](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CurveCoveringBridge.lean)
-/
@[path]
lemma CurveCovering.ellipticIdentity_toCurveMorphismData_RH
-- imply
  CurveCovering.ellipticIdentity.toCurveMorphismData.deg_KX = CurveCovering.ellipticIdentity.toCurveMorphismData.degree * CurveCovering.ellipticIdentity.toCurveMorphismData.deg_KY + CurveCovering.ellipticIdentity.toCurveMorphismData.deg_R :=
-- proof
  CurveCovering.ellipticIdentity.toCurveMorphismData_satisfies_RH

/--
[CurveCovering.toCurveCoverData_satisfies_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CurveCoveringBridge.lean)
-/
@[path]
lemma CurveCovering.toCurveCoverData_satisfies_decomp
  {C : CurveCovering} :
-- imply
  C.toCurveCoverData.morphism.deg_KX = C.toCurveCoverData.morphism.degree * C.toCurveCoverData.morphism.deg_KY + C.toCurveCoverData.morphism.deg_R :=
-- proof
  C.toCurveMorphismData_satisfies_RH

/--
[CurveCovering.genus_form_via_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CurveCoveringBridge.lean)
-/
@[path]
lemma CurveCovering.genus_form_via_bridge
  {C : CurveCovering} :
-- imply
  2 * C.X.g - 2 = C.n * (2 * C.Y.g - 2) + C.deg_R := by
-- proof
  have h := riemann_hurwitz_genus_form C.toCurveCoverData C.toCurveCoverData_satisfies_decomp
  exact h

/--
[CurveCovering.genus_lower_bound_via_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CurveCoveringBridge.lean)
-/
@[path]
lemma CurveCovering.genus_lower_bound_via_bridge
  {C : CurveCovering} :
-- imply
  2 * C.X.g - 2 ≥ C.n * (2 * C.Y.g - 2) := by
-- proof
  have h := riemann_hurwitz_genus_lower_bound_cover C.toCurveCoverData
    C.toCurveCoverData_satisfies_decomp
  exact h

/--
[CurveCovering.bridge_agrees_with_direct](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CurveCoveringBridge.lean)
-/
@[path]
lemma CurveCovering.bridge_agrees_with_direct
  {C : CurveCovering} :
-- imply
  C.genus_form_via_bridge = C.riemann_hurwitz_genus :=
-- proof
  rfl


-- created on 2026-10-23
