import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Padics.MoritaGamma
open MetaMathlibExt


/--
[moritaGammaNat_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/MoritaGamma.lean)
-/
@[path]
private lemma moritaGammaNat_zero_eq
  {p : ℕ} [Fact p.Prime] :
-- imply
  moritaGammaNat p 0 = 1 := by
-- proof
  apply MetaMathlibExt.moritaGammaNat_zero p

/--
[IsMoritaPadicGamma.zero_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/MoritaGamma.lean)
-/
@[path]
private lemma IsMoritaPadicGamma_zero_eq_eq
  {p : ℕ} [Fact p.Prime]
  {Γ : C(PadicInt p, PadicInt p)}
-- given
  (hΓ : IsMoritaPadicGamma p Γ) :
-- imply
  Γ 0 = 1 := by
-- proof
  apply MetaMathlibExt.IsMoritaPadicGamma.zero_eq hΓ

/--
[IsMoritaPadicGamma.natCast_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/MoritaGamma.lean)
-/
@[path]
private lemma IsMoritaPadicGamma_natCast_eq_eq
  {p : ℕ} [Fact p.Prime]
  {Γ : C(PadicInt p, PadicInt p)}
  {n : ℕ}
-- given
  (hΓ : IsMoritaPadicGamma p Γ)
  (hn : 0 < n) :
-- imply
  Γ (n : PadicInt p) = moritaGammaNat p n := by
-- proof
  apply MetaMathlibExt.IsMoritaPadicGamma.natCast_eq hΓ hn

/--
[IsMoritaPadicGamma.isUnit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/MoritaGamma.lean)
-/
@[path]
private lemma IsMoritaPadicGamma_isUnit_eq
  {p : ℕ} [Fact p.Prime]
  {Γ : C(PadicInt p, PadicInt p)}
  {x : PadicInt p}
-- given
  (hΓ : IsMoritaPadicGamma p Γ) :
-- imply
  IsUnit (Γ x) := by
-- proof
  apply MetaMathlibExt.IsMoritaPadicGamma.isUnit hΓ x


-- created on 2026-10-20
