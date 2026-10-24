import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Padics.MoritaGamma
open MetaMathlibExt


namespace MetaMathlibExt

/--
[moritaGammaNat_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/MoritaGamma.lean)
-/
@[path]
lemma moritaGammaNat_zero
  {p : ℕ} [Fact p.Prime] :
-- imply
  moritaGammaNat p 0 = 1 := by
-- proof
  simp [moritaGammaNat]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsMoritaPadicGamma.zero_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/MoritaGamma.lean)
-/
@[path]
lemma IsMoritaPadicGamma.zero_eq
  {p : ℕ} [Fact p.Prime]
  {Γ : C(PadicInt p, PadicInt p)}
-- given
  (hΓ : IsMoritaPadicGamma p Γ) :
-- imply
  Γ 0 = 1 :=
-- proof
  hΓ.1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsMoritaPadicGamma.natCast_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/MoritaGamma.lean)
-/
@[path]
lemma IsMoritaPadicGamma.natCast_eq
  {p : ℕ} [Fact p.Prime]
  {Γ : C(PadicInt p, PadicInt p)}
  {n : ℕ}
-- given
  (hΓ : IsMoritaPadicGamma p Γ)
  (hn : 0 < n) :
-- imply
  Γ (n : PadicInt p) = moritaGammaNat p n :=
-- proof
  hΓ.2.1 n hn

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsMoritaPadicGamma.isUnit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/MoritaGamma.lean)
-/
@[path]
lemma IsMoritaPadicGamma.isUnit
  {p : ℕ} [Fact p.Prime]
  {Γ : C(PadicInt p, PadicInt p)}
  {x : PadicInt p}
-- given
  (hΓ : IsMoritaPadicGamma p Γ) :
-- imply
  IsUnit (Γ x) :=
-- proof
  hΓ.2.2 x

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
