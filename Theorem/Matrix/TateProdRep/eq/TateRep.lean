module

public import Theorem.RingHom.FunctionField
public import Theorem.Valuation.DivisorClassGroup
public import Theorem.WeierstrassCurve.JZeroTateModule
public import Initialize.Tactic.Attr.Basic

public section

set_option autoImplicit false
open scoped TensorProduct


namespace DrinfeldCurve

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k]
  [IsDomain (CoordRing q k)] (ℓ : ℕ) [Fact ℓ.Prime] (E : Type*) [Field E]
  [Algebra ℚ_[ℓ] E]


@[path]
private theorem main
-- given
  (h : hSubgroup q)
  (S : Type)
  (v : tateProd q k ℓ E S)
  (s : S) :
-- imply
  tateProdRep q k ℓ E S h v s = tateRep q k ℓ E h (v s) := by
-- proof
  rfl

end DrinfeldCurve


-- created on 2026-10-24
