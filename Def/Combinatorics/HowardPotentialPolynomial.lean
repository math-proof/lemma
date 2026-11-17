/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/HowardPotentialPolynomial.lean -/

module

public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Def.Combinatorics.Enumerative.PartialBellPolynomial
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Combinatorics.Enumerative.Bell
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

-- Helper lemmas for the proof below (degree bound for the RHS sum).
-- The remaining hard step is the pointwise evaluation identity, which needs a
-- Bell-polynomial / power-series coefficient identity with no Mathlib API.


namespace MetaMathlibExt

open scoped BigOperators

section

noncomputable def howardG : PowerSeries Rat :=
  PowerSeries.mk (fun k => (2 : Rat) / (((k + 2).factorial : Rat)))

noncomputable def howardRsummand (n i : ℕ) : Polynomial Rat :=
  Polynomial.C (((-1 : Rat) ^ i) * ((2 : Rat) ^ i) *
      (((n.factorial : Rat) * (i.factorial : Rat)) / (((n + 2 * i).factorial : Rat)))) *
    ((ascPochhammer Rat i) * Polynomial.C (((i.factorial : Rat))⁻¹)) *
    (((descPochhammer Rat (n - i)).comp (Polynomial.X + Polynomial.C (n : Rat))) *
      Polynomial.C ((((n - i).factorial : Rat))⁻¹)) *
    Polynomial.C (MetaMathlibExt.partialBellPolynomial (n + 2 * i) i
      (fun j => if 2 ≤ j then (1 : Rat) else 0))

noncomputable def howardR (n : ℕ) : Polynomial Rat :=
  Finset.sum (Finset.range (n + 1)) (fun i => howardRsummand n i)

noncomputable def howardBellC : ℕ → Rat :=
  fun m => if m = 1 then 0 else ((m.factorial : Rat)⁻¹)

noncomputable def howardCSeries : PowerSeries Rat :=
  PowerSeries.mk (fun m => if m = 0 then 0 else howardBellC m)

noncomputable def howardH (n : ℕ) : ℕ → Rat :=
  fun k => PowerSeries.coeff n ((howardG⁻¹ ^ n) * (howardG ^ k))

noncomputable def howardP (n : ℕ) : Polynomial Rat :=
  Finset.sum (Finset.range (n + 1)) (fun k =>
    Polynomial.C ((fwdDiff (1 : ℕ))^[k] (howardH n) 0 / (k.factorial : Rat))
      * (descPochhammer Rat k))

noncomputable def howardQ (n : ℕ) : Polynomial Rat :=
  Polynomial.C (n.factorial : Rat)
    * ((howardP n).comp (Polynomial.C (n : Rat) - Polynomial.X))

end

end MetaMathlibExt

namespace MetaMathlibExt

section

end

def bellReindex (N : ℕ) (m : Fin (N + 1) → ℕ) : ℕ → ℕ
  | 0 => 0
  | Nat.succ i => if h : i < N then m ⟨i, by omega⟩ else 0

def mExt (N : ℕ) (m : Fin (N + 1) → ℕ) : ℕ → ℕ :=
  fun i => if h : i < N + 1 then m ⟨i, h⟩ else 0

/-- Inverse reindexing: piAntidiag function to Bell multiplicity vector. -/
def eToBell (N : ℕ) (e : ℕ → ℕ) : Fin (N + 1) → ℕ :=
  fun j => e (j.val + 1)

/-- Auxiliary polynomial `Q` for interpolation: `n! * Σ d_j * desc_j(X+n)/j!`. -/
noncomputable def howardQGen (n : ℕ) {K : Type*} [Field K] (d : ℕ → K) : Polynomial K :=
  Polynomial.C (n.factorial : K) * ∑ j ∈ Finset.range (n + 1),
    Polynomial.C (d j) * (((descPochhammer K j).comp
      (Polynomial.X + Polynomial.C (n : K))) * Polynomial.C (((j.factorial : K))⁻¹))

end MetaMathlibExt
