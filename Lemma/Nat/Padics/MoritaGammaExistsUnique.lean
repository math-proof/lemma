import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Padics.MoritaGammaExistsUnique
open MetaMathlibExt


/--
[existsUnique_moritaPadicGamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/MoritaGammaExistsUnique.lean)
-/
@[path]
private lemma existsUnique_moritaPadicGamma_eq
  {p : ℕ} [Fact p.Prime]
-- given
  (hp : p ≠ 2) :
-- imply
  ∃! Γ : C(PadicInt p, PadicInt p), IsMoritaPadicGamma p Γ := by
-- proof
  apply MetaMathlibExt.existsUnique_moritaPadicGamma p hp


-- created on 2026-10-20
