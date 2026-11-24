module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.v1.Atlas.ArithmeticGeometry.code.HilbertPrimitiveSolutions.Part2
open HilbertSymbol PadicInt in hilbertSymbol
open scoped Classical
open PadicInt HilbertSymbol


public section

/--
[legendreSym_val_local](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
section TwoAdicBridgeLocal
open PadicInt HilbertSymbol

/--
[hasPrimSolMod8_one_eq_local](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
end TwoAdicBridgeLocal
open HilbertSymbol PadicInt in
/-- Half of bilinearity over $\mathbb{Q}_2$: if $(a, c)_{\mathbb{Q}_2} = (b, c)_{\mathbb{Q}_2} = -1$,
then $(ab, c)_{\mathbb{Q}_2} = 1$. Reduced via the $p$-adic decomposition and the closed-form
formula to the verified bilinearity lemma `formula_mul_left_core`. -/
section Nondeg2Adic_Computational
attribute [-instance] Classical.propDecidable
/-- Local copy (within this `Nondeg2Adic_Computational` section, with classical decidability
disabled) of the decidable predicate for primitive mod-$8$ solvability of
$z^2 = u_0 x^2 + v_0 y^2$. -/
@[reducible] def hasPrimSolMod8_one_loc (u₀ v₀ : (ZMod (2 ^ 3))ˣ) : Prop :=
  ∃ x₀ y₀ z₀ : ZMod (2 ^ 3),
    (IsUnit x₀ ∨ IsUnit y₀ ∨ IsUnit z₀) ∧
    z₀ ^ 2 = (↑u₀ : ZMod (2 ^ 3)) * x₀ ^ 2 + (↑v₀ : ZMod (2 ^ 3)) * y₀ ^ 2
/-- Local copy (within `Nondeg2Adic_Computational`) of the decidable predicate for primitive
mod-$8$ solvability of $z^2 = 2 u_0 x^2 + v_0 y^2$. -/
@[reducible] def hasPrimSolMod8_two_loc (u₀ v₀ : (ZMod (2 ^ 3))ˣ) : Prop :=
  ∃ x₀ y₀ z₀ : ZMod (2 ^ 3),
    (IsUnit x₀ ∨ IsUnit y₀ ∨ IsUnit z₀) ∧
    z₀ ^ 2 = (2 : ZMod (2 ^ 3)) * (↑u₀ : ZMod (2 ^ 3)) * x₀ ^ 2 +
      (↑v₀ : ZMod (2 ^ 3)) * y₀ ^ 2

/--
[nondeg_mod8_unit_witness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[reducible] def nondeg_two_prop (w₀ : (ZMod (2 ^ 3))ˣ) : Prop :=
  ∃ (v₀ : (ZMod (2 ^ 3))ˣ), ¬ hasPrimSolMod8_two_loc w₀ v₀

/--
[nondeg_mod8_two_witness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
end Nondeg2Adic_Computational
open HilbertSymbol

/--
[toZMod8Unit_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
namespace hilbertSymbol

/--
[symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
end hilbertSymbol

namespace hilbertSymbol

/--
[mul_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
end hilbertSymbol

namespace hilbertSymbol

/--
[mul_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
end hilbertSymbol

/--
[real_unit_not_square_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
