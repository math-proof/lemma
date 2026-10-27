import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec19CanonicalBundle
open KaehlerDifferential Module PicardProjective


/--
[canonicalModule_rank_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec19CanonicalBundle.lean)
-/
@[path]
lemma canonicalModule_rank_one
  {k : Type u}
  [Field k]
  {d : ℕ} :
-- imply
  Module.finrank (MvPolynomial (Fin (d + 1)) k) (canonicalModule k d) = 1 := by
-- proof
  unfold canonicalModule
  rw [exteriorPower.finrank_eq,
    Module.finrank_eq_card_basis (mvPolynomialBasis k (Fin (d + 1))),
    Fintype.card_fin, Nat.choose_self]

/--
[canonicalModule_free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec19CanonicalBundle.lean)
-/
@[path]
lemma canonicalModule_free
  {k : Type u}
  [Field k]
  {d : ℕ} :
-- imply
  Module.Free (MvPolynomial (Fin (d + 1)) k) (canonicalModule k d) := by
-- proof
  unfold canonicalModule; exact inferInstance
/-- The canonical sheaf `ω_{ℙⁿ}` viewed as an element of the graded Picard group of `ℙⁿ`. -/


-- created on 2026-10-23
