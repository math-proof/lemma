module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.v1.Atlas.Buildings.code.CoxeterGroup.Reflections
public import Def.v1.Atlas.Buildings.code.CoxeterGroup.CoxeterHomomorphism
public import Theorem.Real.GetCoxeterRepresentationMulMul_Simple.eq.GeneralizedReflection_CoxeterRepresentation_E
open Finset BigOperators


public section

namespace CoxeterGroup

/--
[conjugation_reflection_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/RootConjugacy.lean)
-/
@[path]
theorem conjugation_reflection_identity
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {w u : W}
  {s : B}
  {v : B → ℝ} :
-- imply
  let α := (coxeterRepresentation M cs u) (e s)
  let s_α := u * cs.simple s * u⁻¹
  let β := (coxeterRepresentation M cs w) α
  (coxeterRepresentation M cs (w * s_α * w⁻¹)) v = generalizedReflection M β v := by
-- proof
  simp only []
  have hconj : w * (u * cs.simple s * u⁻¹) * w⁻¹ =
    (w * u) * cs.simple s * (w * u)⁻¹ := by group
  rw [hconj]
  have hβ : (coxeterRepresentation M cs w) ((coxeterRepresentation M cs u) (e s)) =
    (coxeterRepresentation M cs (w * u)) (e s) := by
    rw [map_mul (coxeterRepresentation M cs) w u, LinearEquiv.mul_apply]
  rw [hβ]
  exact conj_simpleReflection_eq_generalizedReflection (M := M) (cs := cs) (w := w * u) (s := s) v

end CoxeterGroup


-- created on 2026-10-23
