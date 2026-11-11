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
import Lean.Elab.Term
open Nat Lean
open scoped BigOperators


/-- Path/sequence notation `f ⬝ᵥ g` for `Dot.dot` (typically `∑' t, f t * g t`).
Hooks Mathlib's `⬝ᵥ` glyph: try `Dot.dot` first (infinite path tsums, no `Fintype`), then fall back
to Mathlib `dotProduct` for finite-index vectors. -/
syntax (name := pathDotV) (priority := high) term:72 " ⬝ᵥ " term:73 : term

open Lean Elab Term Meta in
@[term_elab pathDotV]
def elabPathDotV : TermElab := fun stx expectedType? => do
  match stx with
  | `($x ⬝ᵥ $y) => do
    let saved ← saveState
    try
      withoutErrToSorry do
        let e ← elabTerm (← `(Dot.dot $x $y)) expectedType?
        synthesizeSyntheticMVarsNoPostponing
        return e
    catch _ =>
      saved.restore
      elabTerm (← `(dotProduct $x $y)) expectedType?
  | _ => throwUnsupportedSyntax

instance (priority := low) [Add α] [Zero α] [Mul α] : Dot (List.Vector α m) (List.Vector α n) α where
  dot v1 v2 :=
    let n := m ⊔ n
    (v1.resize n * v2.resize n).sum

/-- Infinite-sequence (path) dot product: `f ⬝ᵥ g = ∑' t, f t * g t`.
Specializes to `(ℕ → ℝ) ⬝ᵥ (ℕ → ℝ)` for discounted returns, e.g. `(γ ^ ·) ⬝ᵥ r`. -/
noncomputable instance (priority := low) instDotNatArrow
    [TopologicalSpace α] [AddCommMonoid α] [Mul α] : Dot (ℕ → α) (ℕ → α) α where
  dot f g := ∑' t, f t * g t

/-- Pointwise path-dot against a process: `(f ⬝ᵥ x) ω = f ⬝ᵥ (fun k ↦ x k ω)`.
Lets `(γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]` be an `Ω → α` (discounted return as a random variable). -/
noncomputable instance (priority := low) instDotNatArrowProcess
    {Ω : Type*} [TopologicalSpace α] [AddCommMonoid α] [Mul α] :
    Dot (ℕ → α) (ℕ → Ω → α) (Ω → α) where
  dot f x := fun ω ↦ f ⬝ᵥ (fun k ↦ x k ω)

/-- Path dot when the right factor is `ℕ ⇀ α`, e.g. in `𝔼[r:…]((γ ^ id) ⬝ᵥ r)`. -/
noncomputable instance (priority := low) instDotNatFun
    [TopologicalSpace α] [AddCommMonoid α] [Mul α] : Dot (ℕ → α) (ℕ ⇀ α) α where
  dot f g := f ⬝ᵥ g.toFun

/-- Path-smul sum: `f ⬝ᵥ g = ∑' t, f t • g t` (scalar sequence against a vector sequence).
Lower priority than the Mul-based `(ℕ → α) ⬝ᵥ (ℕ → α)` so scalar `⬝ᵥ` stays unambiguous. -/
noncomputable instance (priority := 50) instDotNatArrowSMul
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [SMul ℝ E] :
    Dot (ℕ → ℝ) (ℕ → E) E where
  dot f g := ∑' t, f t • g t

/-- Pointwise path-smul sum: `(f ⬝ᵥ x) ω = f ⬝ᵥ (fun t ↦ x t ω)`. -/
noncomputable instance (priority := 50) instDotNatArrowSMulProcess
    {E : Type*} {Ω : Type*} [TopologicalSpace E] [AddCommMonoid E] [SMul ℝ E] :
    Dot (ℕ → ℝ) (ℕ → Ω → E) (Ω → E) where
  dot f x := fun ω ↦ f ⬝ᵥ (fun t ↦ x t ω)

/-- Path-smul when the right factor is `ℕ ⇀ E`. -/
noncomputable instance (priority := 50) instDotNatFunSMul
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [SMul ℝ E] :
    Dot (ℕ → ℝ) (ℕ ⇀ E) E where
  dot f g := f ⬝ᵥ g.toFun

/-- Finite FinsetPow dot: `(γ ^ s) ⬝ᵥ g = ∑ i ∈ s, γ^i * g i`. -/
instance (priority := 100) instDotFinsetPow
    [AddCommMonoid α] [HPow α ℕ α] [Mul α] :
    Dot (FinsetPow α) (ℕ → α) α where
  dot p g := ∑ i ∈ p.support, (p.base ^ i) * g i

/-- Pointwise: `((γ ^ s) ⬝ᵥ x) ω = (γ ^ s) ⬝ᵥ (fun i ↦ x i ω)`. -/
instance (priority := 100) instDotFinsetPowProcess
    {Ω : Type*} [AddCommMonoid α] [HPow α ℕ α] [Mul α] :
    Dot (FinsetPow α) (ℕ → Ω → α) (Ω → α) where
  dot p x := fun ω ↦ p ⬝ᵥ (fun i ↦ x i ω)

