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
import Def.Data.Vector.Basic.Part2
open Nat Lean
open scoped BigOperators


instance (priority := low) [Add α] [Zero α] [Mul α] : Dot (List.Vector α m) (List.Vector α n) α where
  dot v1 v2 :=
    let n := m ⊔ n
    (v1.resize n * v2.resize n).sum

/-- Infinite-sequence (path) dot product: `f @ g = ∑' t, f t * g t`.
Specializes to `(ℕ → ℝ) @ (ℕ → ℝ)` for discounted returns, e.g. `(γ ^ ·) @ r`. -/
noncomputable instance (priority := low) instDotNatArrow
    [TopologicalSpace α] [AddCommMonoid α] [Mul α] : Dot (ℕ → α) (ℕ → α) α where
  dot f g := ∑' t, f t * g t

/-- Pointwise path-dot against a process: `(f @ x) ω = f @ (fun k ↦ x k ω)`.
Lets `(γ ^ (id : ℕ → ℕ)) @ r[t:]` be an `Ω → α` (discounted return as a random variable). -/
noncomputable instance (priority := low) instDotNatArrowProcess
    {Ω : Type*} [TopologicalSpace α] [AddCommMonoid α] [Mul α] :
    Dot (ℕ → α) (ℕ → Ω → α) (Ω → α) where
  dot f x := fun ω ↦ f @ (fun k ↦ x k ω)

/-- Path dot when the right factor is `Fun ℕ α` (`ℕ ⇀ α`), e.g. in `𝔼[r:…]((γ ^ id) @ r)`. -/
noncomputable instance (priority := low) instDotNatFun
    [TopologicalSpace α] [AddCommMonoid α] [Mul α] : Dot (ℕ → α) (Fun ℕ α) α where
  dot f g := f @ g.toFun

/-- Path-smul sum: `f @ g = ∑' t, f t • g t` (scalar sequence against a vector sequence).
Lower priority than the Mul-based `(ℕ → α) @ (ℕ → α)` so scalar `@` stays unambiguous. -/
noncomputable instance (priority := 50) instDotNatArrowSMul
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [SMul ℝ E] :
    Dot (ℕ → ℝ) (ℕ → E) E where
  dot f g := ∑' t, f t • g t

/-- Pointwise path-smul sum: `(f @ x) ω = f @ (fun t ↦ x t ω)`. -/
noncomputable instance (priority := 50) instDotNatArrowSMulProcess
    {E : Type*} {Ω : Type*} [TopologicalSpace E] [AddCommMonoid E] [SMul ℝ E] :
    Dot (ℕ → ℝ) (ℕ → Ω → E) (Ω → E) where
  dot f x := fun ω ↦ f @ (fun t ↦ x t ω)

/-- Path-smul when the right factor is `Fun ℕ E`. -/
noncomputable instance (priority := 50) instDotNatFunSMul
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [SMul ℝ E] :
    Dot (ℕ → ℝ) (Fun ℕ E) E where
  dot f g := f @ g.toFun

/-- Finite FinsetPow dot: `(γ ^ s) @ g = ∑ i ∈ s, γ^i * g i`. -/
instance (priority := 100) instDotFinsetPow
    [AddCommMonoid α] [HPow α ℕ α] [Mul α] :
    Dot (FinsetPow α) (ℕ → α) α where
  dot p g := ∑ i ∈ p.support, (p.base ^ i) * g i

/-- Pointwise: `((γ ^ s) @ x) ω = (γ ^ s) @ (fun i ↦ x i ω)`. -/
instance (priority := 100) instDotFinsetPowProcess
    {Ω : Type*} [AddCommMonoid α] [HPow α ℕ α] [Mul α] :
    Dot (FinsetPow α) (ℕ → Ω → α) (Ω → α) where
  dot p x := fun ω ↦ p @ (fun i ↦ x i ω)

