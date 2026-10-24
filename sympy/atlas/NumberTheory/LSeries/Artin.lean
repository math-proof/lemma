/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/Artin.lean -/

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.RepresentationTheory.Invariants

/-!
# Artin L-functions

This module defines a raw local determinant factor and formal Euler product from
supplied decomposition, inertia, and Frobenius data for a finite group.
Constructing that arithmetic local data from a number field and proving
absolute convergence for `Re s > 1` are separate problems not asserted here.

The definitions follow the Artin L-function setup in
[K. Krishnamoorthy, *Moments of non-normal number fields -- II*][krishnamoorthy2024],
arXiv:2310.09768, Section 2, § "Artin L functions", Equation
"Artin L function definition" (lines 223-227):
`L(s,ξ) = ∏_{v<∞} det(Id - p^{-s} ξ(σ_w) | V^{I_w})^{-1}` where
`G = Gal(L/ℚ)`, `G_w` is the decomposition subgroup at `w|v`, `I_w ⊲ G_w` is
inertia, `σ_w ∈ G_w/I_w` is Frobenius, and `ξ : G → Aut(V)` is a
finite-dimensional complex representation acting on inertia invariants
`V^{I_w}`.

## Main definitions

* `Representation.ArtinLocalDatum`: decomposition subgroup `G_w ≤ G`, its
  normal inertia subgroup `I_w ≤ G_w`, and Frobenius `σ_w ∈ G_w/I_w` at a
  rational prime `p`.
* `Representation.artinLocalFactorRaw`: the totalized determinant inverse
  `det(Id - p^{-s} ρ(σ_w) | V^{I_w})^{-1}`.
* `Representation.ArtinLocalFactorRegular`: the denominator-nonvanishing domain.
* `Representation.artinEulerProductOfLocalData`: the formal `tprod` over supplied data.
* `Representation.HasArtinEulerProduct`: the explicit convergence/value interface.
* `Representation.HasNonzeroArtinEulerProduct`: convergence to a genuine nonzero value.

## References

[krishnamoorthy2024]: https://doi.org/10.1007/s00605-024-02050-1
-/

namespace Representation

universe u v

variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- Local Galois data for the Artin Euler factor at a rational prime.

For the finite Galois group `G = Gal(L/ℚ)`, `decomposition = G_w` is the
decomposition subgroup at a place `w|p`, `inertia = I_w` is its normal inertia
subgroup, and `frobenius = σ_w ∈ G_w/I_w` is the Frobenius coset.  The
representation is restricted to `G_w` and then `I_w`-invariants are taken,
so `G_w/I_w` acts on `V^{I_w}` and `frobenius` determines the local operator. -/
structure ArtinLocalDatum (G : Type u) [Group G] [Finite G] where
  decomposition : Subgroup G
  inertia : Subgroup decomposition
  [isNormal : inertia.Normal]
  frobenius : decomposition ⧸ inertia

attribute [instance] ArtinLocalDatum.isNormal

/-- The determinant whose inverse is the formal Artin local factor at `p`. -/
noncomputable def artinLocalDenominator (ρ : Representation ℂ G V)
    [Module.Free ℂ V] [Module.Finite ℂ V] (p : Nat.Primes)
    (d : ArtinLocalDatum G) (s : ℂ) : ℂ :=
  LinearMap.det
    (LinearMap.id - ((p.1 : ℂ) ^ (-s)) •
      ((Representation.quotientToInvariants
        (ρ.comp d.decomposition.subtype : Representation ℂ d.decomposition V)
        d.inertia) d.frobenius))

/-- The domain condition saying that the formal local factor has no pole at `s`. -/
def ArtinLocalFactorRegular (ρ : Representation ℂ G V)
    [Module.Free ℂ V] [Module.Finite ℂ V] (p : Nat.Primes)
    (d : ArtinLocalDatum G) (s : ℂ) : Prop :=
  artinLocalDenominator ρ p d s ≠ 0

/-- The totalized inverse of the Artin local denominator at the rational prime `p`.

`ρ` is restricted to the decomposition subgroup and the resulting
`I_w`-invariants carry the quotient action `G_w/I_w`; evaluating that
action at `frobenius` gives the operator whose determinant is inverted.
The hypothesis `[Module.Free ℂ V] [Module.Finite ℂ V]` makes the determinant
available via `LinearMap.det` on the finite-dimensional invariant subspace.
At a zero of the denominator, complex inversion gives the totalized value `0`;
use `ArtinLocalFactorRegular` when a genuine finite Euler factor is required. -/
noncomputable def artinLocalFactorRaw (ρ : Representation ℂ G V)
    [Module.Free ℂ V] [Module.Finite ℂ V] (p : Nat.Primes)
    (d : ArtinLocalDatum G) (s : ℂ) : ℂ :=
  (artinLocalDenominator ρ p d s)⁻¹

/-- The formal Euler product of raw factors attached to supplied local data.

This is deliberately named as an Euler product *of local data*: the input need
not arise from places of a number field, and no conjugacy-independence is asserted.
When the family is not multipliable, `tprod` takes its conventional default value. -/
noncomputable def artinEulerProductOfLocalData (ρ : Representation ℂ G V)
    [Module.Free ℂ V] [Module.Finite ℂ V]
    (localData : Nat.Primes → ArtinLocalDatum G) (s : ℂ) : ℂ :=
  ∏' p, artinLocalFactorRaw ρ p (localData p) s

/-- The raw local factors have the convergent product `z` at `s`. -/
def HasArtinEulerProduct (ρ : Representation ℂ G V)
    [Module.Free ℂ V] [Module.Finite ℂ V]
    (localData : Nat.Primes → ArtinLocalDatum G) (s z : ℂ) : Prop :=
  HasProd (fun p => artinLocalFactorRaw ρ p (localData p) s) z

/-- The raw local factors have a convergent, nonzero product at `s`.

Unlike `HasArtinEulerProduct`, this predicate rules out both a zero product and
every totalized zero local factor, so it represents a genuine finite Euler-product
value rather than a pole encoded by the raw definitions. -/
def HasNonzeroArtinEulerProduct (ρ : Representation ℂ G V)
    [Module.Free ℂ V] [Module.Finite ℂ V]
    (localData : Nat.Primes → ArtinLocalDatum G) (s z : ℂ) : Prop :=
  HasArtinEulerProduct ρ localData s z ∧ z ≠ 0
end Representation
