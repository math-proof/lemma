import Mathlib
import sympy.Basic
import sympy.Algebra.MvPolynomial.RegularFunction

open MvPolynomial

/--
[Jacobian_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MvPolynomial/RegularFunction.lean)
-/
@[path]
private lemma jacobian
  [CommSemiring k]
-- given
  (F : RegularFunction k σ τ) (j : τ) (i : σ) :
-- imply
  F.Jacobian j i = MvPolynomial.pderiv i (F j) := by
-- proof
  apply RegularFunction.Jacobian_apply


/--
[comp_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MvPolynomial/RegularFunction.lean)
-/
@[path]
private lemma comp_apply_eq
  [CommSemiring k]
-- given
  (G : RegularFunction k τ ι) (F : RegularFunction k σ τ) (i : ι) :
-- imply
  (G.comp F) i = MvPolynomial.bind₁ F (G i) := by
-- proof
  apply RegularFunction.comp_apply


/--
[id_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MvPolynomial/RegularFunction.lean)
-/
@[path]
private lemma id_apply_eq
  [CommSemiring k]
-- given
  (i : σ) :
-- imply
  RegularFunction.id k σ i = MvPolynomial.X i := by
-- proof
  apply RegularFunction.id_apply


/--
[id_comp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MvPolynomial/RegularFunction.lean)
-/
@[path]
private lemma id_comp_eq
  [CommSemiring k]
-- given
  (F : RegularFunction k σ τ) :
-- imply
  (RegularFunction.id k τ).comp F = F := by
-- proof
  apply RegularFunction.id_comp


/--
[comp_id](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MvPolynomial/RegularFunction.lean)
-/
@[path]
private lemma comp_id_eq
  [CommSemiring k]
-- given
  (F : RegularFunction k σ τ) :
-- imply
  F.comp (RegularFunction.id k σ) = F := by
-- proof
  apply RegularFunction.comp_id


/--
[comp_assoc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MvPolynomial/RegularFunction.lean)
-/
@[path]
private lemma comp_assoc_eq
  [CommSemiring k]
-- given
  (H : RegularFunction k ι κ) (G : RegularFunction k τ ι) (F : RegularFunction k σ τ) :
-- imply
  (H.comp G).comp F = H.comp (G.comp F) := by
-- proof
  apply RegularFunction.comp_assoc


/--
[comp_aeval](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MvPolynomial/RegularFunction.lean)
-/
@[path]
private lemma comp_aeval_eq
  [CommSemiring k] [CommSemiring S₁] [Algebra k S₁]
-- given
  (G : RegularFunction k τ ι) (F : RegularFunction k σ τ) (a : σ → S₁) :
-- imply
  (G.comp F).aeval a = G.aeval (F.aeval a) := by
-- proof
  apply RegularFunction.comp_aeval


-- created on 2026-10-09
