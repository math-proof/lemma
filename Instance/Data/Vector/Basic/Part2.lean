import Mathlib.Data.Vector.MapLemmas
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lemma.Nat.EqMin_SubMulS
import Lemma.Nat.EqAddMulDiv
import Lemma.List.LengthRange.eq.Length
import Lemma.List.Prod.eq.MulProdS
import Theorem.Algebra.Power.Part2
import Theorem.Function
import Def.Data.Vector.Basic
open Nat Lean
open scoped BigOperators


namespace List.Vector

/--
substraction is automatically defined by typeclass SubNegMonoid:
instance [Sub α] : Sub (Vector α n)
-/
instance [Add α] : Add (Vector α n) where
  add a b := a.map₂ HAdd.hAdd b

instance [Add α] : HAdd (Vector α n) α (Vector α n) where
  hAdd a b := a.map (· + b)

instance [Sub α] : HSub (Vector α n) α (Vector α n) where
  hSub a b := a.map (· - b)

instance [Mul α] : Mul (Vector α n) where
  mul a b := a.map₂ HMul.hMul b

instance [HPow α β α] : HPow (Vector α n) (Vector β n) (Vector α n) where
  hPow a b := a.map₂ HPow.hPow b

instance [Mul α] : HMul (Vector α n) α (Vector α n) where
  hMul a b := a.map (· * b)

instance [Mul α] : HMul α (Vector α n) (Vector α n) where
  hMul a b := b.map (a * ·)

instance [Div α] : Div (Vector α n) where
  div a b := a.map₂ HDiv.hDiv b

instance [Div α] : HDiv (Vector α n) α (Vector α n) where
  hDiv a b := a.map (· / b)

instance [Zero α] : Zero (Vector α n) where
  zero := Vector.replicate n 0

instance [One α] : One (Vector α n) where
  one := Vector.replicate n 1

instance [Neg α] : Neg (Vector α n) where
  neg a := a.map (-·)

instance [Inv α] : Inv (Vector α n) where
  inv a := a.map (·⁻¹)

instance [LE α] : LE (Vector α n) where
  le a b := ∀ (i : Fin n), a[i] ≤ b[i]

instance [LT α] : LT (Vector α n) where
  lt a b := ∀ (i : Fin n), a[i] < b[i]

instance (priority := low) [Coe α β] : Coe (Vector α n) (Vector β n) where
  coe v := v.map Coe.coe

instance [NatCast α] : NatCast (Vector α n) where
  natCast a := List.Vector.replicate n a

instance [NNRatCast α] : NNRatCast (Vector α n) where
  nnratCast q := List.Vector.replicate n (NNRatCast.nnratCast q)

end List.Vector
