import Lemma.Int.Mul.ge.Zero.is.AndGeS_0.ou.AndLeS_0
open Int


@[main]
private lemma main
  [Semiring α]
  [LinearOrder α]
  [ExistsAddOfLE α]
  [MulPosStrictMono α]
  [PosMulStrictMono α]
  [AddLeftReflectLE α]
  [AddLeftMono α]
  {a b : α}
-- given
  (h₀ : a ≤ 0)
  (h₁ : b ≤ 0) :
-- imply
  a * b ≥ 0 := by
-- proof
  rw [Mul.ge.Zero.is.AndGeS_0.ou.AndLeS_0]
  exact Or.inr ⟨h₀, h₁⟩


-- created on 2025-03-23
