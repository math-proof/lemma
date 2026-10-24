/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol/Units.lean -/

import sympy.atlas.NumberTheory.Padics.HilbertSymbol
import Lemma.Nat.Padics.HilbertSymbol
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Hilbert symbols of p-adic integer units

For an odd prime p, the p-adic Hilbert symbol is trivial on p-adic integer units. The proof finds
a solution modulo p by Chevalley-Warning and lifts it using Hensel lemma.
-/

set_option autoImplicit false

namespace HilbertSymbol

/-- Inclusion of p-adic integer units into p-adic field units. -/
noncomputable def unitZpToQp {p : ℕ} [Fact (Nat.Prime p)]
    (u : ℤ_[p]ˣ) : ℚ_[p]ˣ :=
  Units.map (PadicInt.Coe.ringHom (p := p)).toMonoidHom u
end HilbertSymbol
