import Mathlib
import sympy.Basic
import Def.v1.Atlas.EllipticCurves.code.DualIsogeny
open WeierstrassCurve.Affine DualIsogeny DualIsogenyExt IsogenyDecomposition


namespace DualIsogeny

/--
[dualIsogeny_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DualIsogeny.lean)
-/
@[path]
lemma dualIsogeny_comp
  [Field F]
  [DecidableEq F]
  {E₁ E₂ : WeierstrassCurve.Affine F}
  {α : Isogeny E₁ E₂} :
-- imply
  (dualIsogeny α).toAddMonoidHom.comp α.toAddMonoidHom = multiplicationByN E₁ (α.degree : ℤ) :=
-- proof
  α.dualIsogeny_comp

end DualIsogeny

namespace DualIsogeny

/--
[dualIsogeny_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DualIsogeny.lean)
-/
@[path]
lemma dualIsogeny_unique
  [Field F]
  [DecidableEq F]
  {E₁ E₂ : WeierstrassCurve.Affine F}
  {α : Isogeny E₁ E₂}
  {β : Isogeny E₂ E₁}
-- given
  (hβ : β.toAddMonoidHom.comp α.toAddMonoidHom = multiplicationByN E₁ (α.degree : ℤ)) :
-- imply
  β = dualIsogeny α := by
-- proof
  exact Isogeny.ext
    (α.dualIsogeny_unique β hβ)
    ((α.degree_of_dual_property β hβ).trans α.degree_dualIsogeny.symm)

end DualIsogeny

namespace DualIsogeny

/--
[comp_dualIsogeny](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DualIsogeny.lean)
-/
@[path]
lemma comp_dualIsogeny
  [Field F]
  [DecidableEq F]
  {E₁ E₂ : WeierstrassCurve.Affine F}
  {α : Isogeny E₁ E₂} :
-- imply
  α.toAddMonoidHom.comp (dualIsogeny α).toAddMonoidHom = multiplicationByN E₂ (α.degree : ℤ) :=
-- proof
  α.comp_dualIsogeny

end DualIsogeny

namespace DualIsogeny

/--
[degree_dualIsogeny](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DualIsogeny.lean)
-/
@[path]
lemma degree_dualIsogeny
  [Field F]
  [DecidableEq F]
  {E₁ E₂ : WeierstrassCurve.Affine F}
  {α : Isogeny E₁ E₂} :
-- imply
  (dualIsogeny α).degree = α.degree :=
-- proof
  α.degree_dualIsogeny

end DualIsogeny

namespace DualIsogeny

/--
[dualIsogeny_dualIsogeny](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DualIsogeny.lean)
-/
@[path]
lemma dualIsogeny_dualIsogeny
  [Field F]
  [DecidableEq F]
  {E₁ E₂ : WeierstrassCurve.Affine F}
  {α : Isogeny E₁ E₂} :
-- imply
  (dualIsogeny (dualIsogeny α)).toAddMonoidHom = α.toAddMonoidHom :=
-- proof
  α.dualIsogeny_dualIsogeny

end DualIsogeny

namespace DualIsogeny

/--
[multiplicationByN_self_dual](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DualIsogeny.lean)
-/
@[path]
lemma multiplicationByN_self_dual
  [Field F]
  [DecidableEq F]
  {E₁ E₂ : WeierstrassCurve.Affine F}
  {E : WeierstrassCurve.Affine F}
  {n : ℤ}
-- given
  (hn : n ≠ 0) :
-- imply
  (Isogeny.multiplicationByN_isogeny E n hn).dualIsogeny.toAddMonoidHom = multiplicationByN E n :=
-- proof
  Isogeny.multiplicationByN_self_dual E n hn
end DualIsogeny
namespace DualIsogenyExt
variable {F : Type*} [Field F] [DecidableEq F]
variable {E₁ E₂ : WeierstrassCurve.Affine F}
open WeierstrassCurve.Affine


namespace DualIsogenyExt

/--
[IsogenyOrZero.dual_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DualIsogeny.lean)
-/
@[path]
lemma IsogenyOrZero.dual_zero
  [Field F]
  [DecidableEq F]
  {E₁ E₂ : WeierstrassCurve.Affine F} :
-- imply
  (IsogenyOrZero.zero : IsogenyOrZero E₁ E₂).dual = IsogenyOrZero.zero :=
-- proof
  rfl

end DualIsogenyExt

namespace DualIsogenyExt

/--
[IsogenyOrZero.deg_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DualIsogeny.lean)
-/
@[path]
lemma IsogenyOrZero.deg_zero
  [Field F]
  [DecidableEq F]
  {E₁ E₂ : WeierstrassCurve.Affine F} :
-- imply
  (IsogenyOrZero.zero : IsogenyOrZero E₁ E₂).deg = 0 :=
-- proof
  rfl

end DualIsogenyExt

namespace DualIsogenyExt

/--
[IsogenyOrZero.dual_ofIsogeny](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DualIsogeny.lean)
-/
@[path]
lemma IsogenyOrZero.dual_ofIsogeny
  [Field F]
  [DecidableEq F]
  {E₁ E₂ : WeierstrassCurve.Affine F}
  {α : Isogeny E₁ E₂} :
-- imply
  (IsogenyOrZero.ofIsogeny α).dual = IsogenyOrZero.ofIsogeny α.dualIsogeny :=
-- proof
  rfl

end DualIsogenyExt

namespace DualIsogenyExt

/--
[IsogenyOrZero.deg_ofIsogeny](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DualIsogeny.lean)
-/
@[path]
lemma IsogenyOrZero.deg_ofIsogeny
  [Field F]
  [DecidableEq F]
  {E₁ E₂ : WeierstrassCurve.Affine F}
  {α : Isogeny E₁ E₂} :
-- imply
  (IsogenyOrZero.ofIsogeny α).deg = α.degree :=
-- proof
  rfl
end DualIsogenyExt
namespace IsogenyDecomposition

end DualIsogenyExt

namespace IsogenyDecomposition

/--
[isogeny_prime_factor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DualIsogeny.lean)
-/
@[path]
lemma isogeny_prime_factor
  [Field F]
  [DecidableEq F]
  {E₁ E₂ : WeierstrassCurve.Affine F}
  {α : Isogeny E₁ E₂}
  {p : ℕ}
-- given
  (hdeg : 1 < α.degree)
  (hp : Nat.Prime p)
  (hdvd : p ∣ α.degree) :
-- imply
  ∃ (E_mid : WeierstrassCurve.Affine F) (β : Isogeny E₁ E_mid) (γ : Isogeny E_mid E₂), β.degree = p ∧ 0 < γ.degree ∧ γ.degree * β.degree = α.degree ∧ γ.toAddMonoidHom.comp β.toAddMonoidHom = α.toAddMonoidHom :=
-- proof
  Isogeny.prime_factor_aux α hdeg p hp hdvd

end IsogenyDecomposition

namespace IsogenyDecomposition

/--
[isogeny_prime_degree_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DualIsogeny.lean)
-/
@[path]
lemma isogeny_prime_degree_decomposition
  [Field F]
  [DecidableEq F]
  {E₁ E₂ : WeierstrassCurve.Affine F}
  {α : Isogeny E₁ E₂}
-- given
  (hdeg : 1 < α.degree) :
-- imply
  ∃ (chain : IsogenyChain E₁ E₂), chain.allPrimeDegree ∧ chain.compose = α.toAddMonoidHom :=
-- proof
  _root_.isogeny_prime_degree_decomposition (F := F) α hdeg

end IsogenyDecomposition


-- created on 2026-10-23
