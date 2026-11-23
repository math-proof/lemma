module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Conditional
public import Def.Probability.SymbolicProbability
public import Def.Probability.JointRv

@[expose] public section

open MeasureTheory
open scoped ProbabilityTheory


/--
Pointwise coercion of a pair of functions on the same domain to a function into pairs:
`↑(x, y) = JointRandomSymbol x y`. A bare pair `(x, y)` is therefore accepted
wherever an `Ω → α × β` is expected — e.g. `let prod : Ω → α × β := (x, y)` — and the
`CoeFun` instance also makes application `(x, y) ω` well-typed. The coe body delegates
to `JointRandomSymbol` (rather than re-using an anonymous `fun`) so typeclass search
sees the same head symbol: e.g. a hypothesis written as a bare pair `(x, y)`
also supplies `SinglePSpace π (x, y)`.
-/
instance Function.coeProdPi {ι α β : Type*} :
    Coe ((ι → α) × (ι → β)) (ι → α × β) :=
  ⟨fun p ↦ JointRandomSymbol p.1 p.2⟩

instance Function.coeFunProdPi {ι α β : Type*} :
    CoeFun ((ι → α) × (ι → β)) (fun _ => ι → α × β) :=
  ⟨fun p ↦ JointRandomSymbol p.1 p.2⟩


/--
Triple variants: a nested pair of functions on the same domain coerces in one step to a
function into nested pairs, in both associations. Coercions do not chain through nested
`Prod.mk` nodes at argument positions, so a bare `((x, y), z)` or `(x, (y, z))` needs these
instances to be accepted where an `Ω → (α × β) × γ` (resp. `Ω → α × (β × γ)`) is expected.
-/
instance Function.coeProdPi3L {ι α β γ : Type*} :
    Coe (((ι → α) × (ι → β)) × (ι → γ)) (ι → (α × β) × γ) :=
  ⟨fun p ↦ JointRandomSymbol (JointRandomSymbol p.1.1 p.1.2) p.2⟩

instance Function.coeProdPi3R {ι α β γ : Type*} :
    Coe ((ι → α) × ((ι → β) × (ι → γ))) (ι → α × (β × γ)) :=
  ⟨fun p ↦ JointRandomSymbol p.1 (JointRandomSymbol p.2.1 p.2.2)⟩

instance Function.coeFunProdPi3L {ι α β γ : Type*} :
    CoeFun (((ι → α) × (ι → β)) × (ι → γ)) (fun _ => ι → (α × β) × γ) :=
  ⟨fun p ↦ JointRandomSymbol (JointRandomSymbol p.1.1 p.1.2) p.2⟩

instance Function.coeFunProdPi3R {ι α β γ : Type*} :
    CoeFun ((ι → α) × ((ι → β) × (ι → γ))) (fun _ => ι → α × (β × γ)) :=
  ⟨fun p ↦ JointRandomSymbol p.1 (JointRandomSymbol p.2.1 p.2.2)⟩


