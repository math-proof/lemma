import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.AlgebraicGeometryI.code.GrothendieckRiemannRoch
open GRR


namespace GRR

/--
[hirzebruch_riemann_roch](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckRiemannRoch.lean)
-/
@[path]
lemma hirzebruch_riemann_roch
  {X : HRRData}
  {α : X.K0X} :
-- imply
  (X.euler_char α : ℚ) = X.degree (X.chern_character α * X.todd_class) :=
-- proof
  X.hrr_formula α
/-- Specialization of GRR when the relative Todd class is trivial: the Chern character commutes
with proper pushforward, i.e. `ch(f_! α) = f_*(ch(α))`. -/

end GRR


-- created on 2026-10-23
