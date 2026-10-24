import Mathlib
import Lemma.Definitions.Def_ModularCurve_PlaceWidth

set_option autoImplicit false

noncomputable section
open AlgebraicCurve ModularCurve

namespace ModularCurve

variable (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]

def SSIndex (hp5 : 5 ≤ p) (k : ℤ) : Type :=
  { x : Place K (modularFunctionFieldC K N) // x ∈ ssPlaces p N K ∧ 2 ≤ k ∧ 2 ∣ k ∧ ((placeWidth N x : ℤ) ∣ k / 2) ∧ 5 ≤ p }

abbrev SSCarrier (hp5 : 5 ≤ p) (k : ℤ) : Type := SSIndex p N K hp5 k → K

def poleOrder (hp5 : 5 ≤ p) (k : ℤ) (x : SSIndex p N K hp5 k) : ℤ :=
  (k / 2) * ((jWidth (x.1.evalAt (jGeomGen K N)) : ℤ) - 1) / (placeWidth N x.1 : ℤ)

omit [Fact p.Prime] [CharP K p] [IsAlgClosed K] [DecidableEq K] in

def unif (x : Place K (modularFunctionFieldC K N)) : modularFunctionFieldC K N :=
  Classical.epsilon (fun π : modularFunctionFieldC K N => x.ord π = 1)

omit [Fact p.Prime] [CharP K p] [IsAlgClosed K] [DecidableEq K] in

def lead (x : Place K (modularFunctionFieldC K N)) (a : ℤ) (f : modularFunctionFieldC K N) : K :=
  x.evalAt (unif N K x ^ a * f)

def resFnFun (hp5 : 5 ≤ p) (m : ℕ) (G : modularFunctionFieldC K N) : SSCarrier p N K hp5 (2 * (m : ℤ)) :=
  fun x => lead N K x.1 (poleOrder p N K hp5 (2 * (m : ℤ)) x) G

end ModularCurve

end
