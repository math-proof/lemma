import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.ArithmeticGeometry.code.JInvariantInK
open WeierstrassCurve


/--
[GenusOneCurve.jInvariant_in_k](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariantInK.lean)
-/
@[path]
lemma GenusOneCurve.jInvariant_in_k
  {k : Type u}
  [Field k]
  {C : GenusOneCurve k}
  {O : C.PointOverAlgClosure} :
-- imply
  (C.ellipticCurveAtBasePoint O).jInvariant ∈ Set.range (algebraMap k (AlgebraicClosure k)) :=
-- proof
  ⟨C.jInvariant, by
    unfold ellipticCurveAtBasePoint EllipticCurveOver.jInvariant GenusOneCurve.jInvariant
    rw [variableChange_j]
    exact (C.Jacobian.curve.map_j (algebraMap k (AlgebraicClosure k))).symm⟩


-- created on 2026-10-23
