/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol/Units.lean -/

module

public import Def.NumberTheory.Padics.HilbertSymbol
public import Theorem.Nat.Padics.HilbertSymbol
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Order
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false

/-!
# Hilbert symbols of p-adic integer units

For an odd prime p, the p-adic Hilbert symbol is trivial on p-adic integer units. The proof finds
a solution modulo p by Chevalley-Warning and lifts it using Hensel lemma.
-/


namespace HilbertSymbol

/-- Inclusion of p-adic integer units into p-adic field units. -/
noncomputable def unitZpToQp {p : ℕ} [Fact (Nat.Prime p)]
    (u : ℤ_[p]ˣ) : ℚ_[p]ˣ :=
  Units.map (PadicInt.Coe.ringHom (p := p)).toMonoidHom u

end HilbertSymbol
