/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyVolcano.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.ZMod.Basic
import sympy.atlas.v1.Atlas.EllipticCurves.code.RingClassField
import Lemma.Complex.Atlas.v1.EllipticCurves.code.RingClassField
import Lemma.Complex.Atlas.v1.EllipticCurves.code.HilbertClassPolynomial
import sympy.atlas.v1.Atlas.EllipticCurves.code.HilbertClassPolynomial

noncomputable section

open Polynomial Finset

/-- A multigraph on vertex set `V`: each unordered pair `(v, w)` carries a
multiplicity `edgeMult v w : ℕ`, required to be symmetric in `v, w`. -/
namespace Multigraph

variable {V : Type*} (G : Multigraph V)

/-- Two vertices `v, w` are adjacent in `G` iff their edge multiplicity is positive. -/
end Multigraph

/-- The classical modular polynomial `Φ_ℓ(X, Y)` specialized to `Y = j₁`: a univariate
polynomial in `X` over `k` whose roots over an algebraic closure are the `j`-invariants
of elliptic curves `ℓ`-isogenous to a curve with `j`-invariant `j₁`. -/
namespace IsogenyGraph

/-- The multiplicity of `j₂` as a root of `Φ_ℓ(j₁, Y)`, equal to the number of
`ℓ`-isogenies (with multiplicity) from a curve with `j`-invariant `j₁` to one with
`j`-invariant `j₂`. -/
abbrev 𝔽_p_jInvariants (p : ℕ) : Type := ZMod p

/-- Edges in the `ℓ`-isogeny graph are symmetric: an `ℓ`-isogeny from `j₁` to `j₂`
gives rise to a dual `ℓ`-isogeny from `j₂` to `j₁`. -/
end IsogenyGraph

/-- An `ℓ`-volcano: a connected multigraph organized into levels (the *surface* is
level `0`, the *floor* is level `depth`). Vertices off the floor have degree `ℓ + 1`,
surface vertices have a prescribed surface degree (`≤ 2`), and non-surface vertices
have a unique parent at the level above. Edges can only join the surface to itself
or adjacent levels. -/
namespace IsogenyVolcano

variable {ℓ : ℕ} (vol : IsogenyVolcano ℓ)

/-- A vertex of the volcano is on the *surface* (or *crater*) iff its level is `0`. -/
def isSurface (v : vol.V) : Prop :=
  vol.level v = ⟨0, Nat.zero_lt_succ _⟩

/-- A vertex of the volcano is on the *floor* iff its level is the maximal one
(`depth`). -/
def isFloor (v : vol.V) : Prop :=
  vol.level v = Fin.last vol.depth

/-- The depth of the volcano (the maximal level index). -/
def volcanoDepth : ℕ := vol.depth

/-- An edge `(v, w)` is *horizontal* iff it has positive multiplicity and both
endpoints lie on the surface. -/
end IsogenyVolcano

namespace CMConductorTrichotomy

/-- Classification (Definition 22.4) of an `ℓ`-isogeny between CM elliptic curves
by the relation between the source and target endomorphism orders: horizontal
(`𝒪 = 𝒪''`), descending (`[𝒪 : 𝒪''] = ℓ`), or ascending (`[𝒪'' : 𝒪] = ℓ`). -/
inductive IsogenyType
  |     horizontal
  |     descending
  |     ascending
  deriving DecidableEq

/-- Classify an `ℓ`-isogeny by comparing source conductor `f` and target conductor
`f'`: `f = f'` is horizontal, `f = ℓ f'` is descending, otherwise ascending. -/
def classifyIsogeny (ℓ f f' : ℕ) : IsogenyType :=
  if f = f' then IsogenyType.horizontal
  else if f = ℓ * f' then IsogenyType.descending
  else IsogenyType.ascending

/-- Data attached to a CM `ℓ`-isogeny problem: an imaginary quadratic discriminant
`D < 0`, a prime `ℓ`, and a positive conductor `f` of the source order. -/
structure CMIsogenyData where
  D : ℤ
  hD_neg : D < 0
  ℓ : ℕ
  hℓ_prime : Nat.Prime ℓ
  f : ℕ
  hf_pos : 0 < f

/-- Counts of `ℓ`-isogenies from a surface (`ℓ ∤ f`) CM elliptic curve, organized by
type. Following Theorem 22.5, there are `1 + (D/ℓ)` horizontal, `ℓ - (D/ℓ)`
descending, and `0` ascending isogenies. -/
structure SurfaceIsogenyCounts (C : CMIsogenyData) where
  hℓ_ndvd_f : ¬(C.ℓ ∣ C.f)
  numHorizontal : ℕ
  numDescending : ℕ
  numAscending : ℕ
  horizontal_eq : (numHorizontal : ℤ) = 1 + jacobiSym C.D C.ℓ
  descending_eq : (numDescending : ℤ) = ↑C.ℓ - jacobiSym C.D C.ℓ
  ascending_eq : numAscending = 0

/-- Counts of `ℓ`-isogenies from a non-surface (`ℓ ∣ f`) CM elliptic curve: `0`
horizontal, `ℓ` descending, and `1` ascending. -/
structure NonSurfaceIsogenyCounts (C : CMIsogenyData) where
  hℓ_dvd_f : C.ℓ ∣ C.f
  numHorizontal : ℕ
  numDescending : ℕ
  numAscending : ℕ
  horizontal_eq : numHorizontal = 0
  descending_eq : numDescending = C.ℓ
  ascending_eq : numAscending = 1

/-- Data for an ordinary component of the `ℓ`-isogeny graph over `𝔽_q`: a prime `ℓ`
coprime to `q`, the Hasse trace `t` (with `t² < 4q`), a fundamental imaginary
quadratic discriminant `D₀`, a positive base conductor `f₀`, and the class number. -/
structure OrdinaryIsogenyComponent where
  q : ℕ
  ℓ : ℕ
  hℓ_prime : Nat.Prime ℓ
  hℓ_ndvd_q : ¬(ℓ ∣ q)
  t : ℤ
  hHasse : t ^ 2 < 4 * (q : ℤ)
  D₀ : ℤ
  hD₀_neg : D₀ < 0
  f₀ : ℕ
  hf₀_pos : 0 < f₀
  classOrder : ℕ
  hClassOrder_pos : 0 < classOrder

/-- Kohel's structural data for an ordinary `ℓ`-volcano: an `IsogenyVolcano` of
prime degree `ℓ`, equipped with a conductor function `f₀ · ℓ^level` on vertices,
crater data tied to the Kronecker symbol `(D₀/ℓ)`, and the depth-determining
equation `4q = t² - ℓ^{2d} v² D₀`. -/
variable {C : OrdinaryIsogenyComponent} (K : KohelVolcano C)

/-- If the Hilbert class polynomial of `D` splits and is separable over `F` with
roots equal to `ellCMSet D F`, then the cardinality of `ellCMSet D F` equals the
class number of `D` (an instance of Deuring's Theorem 21.12). -/
def OrderContains (D D' : ℤ) : Prop :=
  (∃ u : ℤ, 0 < u ∧ D = u ^ 2 * D') ∧ IsImagQuadDiscriminant D'

/-- Data for counting `ℓ`-isogenies from a CM elliptic curve over `𝔽_q`: an
imaginary quadratic discriminant `D` with class data, a prime `ℓ ∤ q` coprime to
`|D|`, and a conductor `f`. -/
structure CMCurveData where
  D : ℤ
  hD : IsImagQuadDiscriminant D
  ℓ : ℕ
  hℓ_prime : Nat.Prime ℓ
  q : ℕ
  hq : 1 < q
  hℓ_ndvd_q : ¬(ℓ ∣ q)
  hcop : Nat.Coprime q D.natAbs
  f : ℕ
  hf_pos : 0 < f

/-- The discriminant of a descendant order, obtained by multiplying `D` by `ℓ²`. -/
def CMCurveData.descendantDisc (C : CMCurveData) : ℤ := C.ℓ ^ 2 * C.D

/-- Counts of `ℓ`-isogenies from a CM elliptic curve over `F` (with `|F| = q`):
horizontal, ascending, and descending counts, with the values prescribed by
Theorem 22.5, and the descending count conditioned on whether descendant CM
curves exist over `F`. -/
structure IsogenyCount (C : CMCurveData) (F : Type*) [Field F] [Fintype F] where
  hcard : Fintype.card F = C.q
  hne : (ellCMSet C.D F).Nonempty
  numHorizontal : ℕ
  numAscending : ℕ
  numDescending : ℕ
  horizontal_eq : (numHorizontal : ℤ) = 1 + jacobiSym C.D C.ℓ
  ascending_eq : numAscending = if C.ℓ ∣ C.f then 1 else 0
  descending_zero_of_empty :
    (ellCMSet C.descendantDisc F) = ∅ → numDescending = 0
  descending_eq_of_nonempty :
    (ellCMSet C.descendantDisc F).Nonempty →
    (numDescending : ℤ) = ↑C.ℓ - jacobiSym C.D C.ℓ

/-- Existence of an `IsogenyCount` package for any CM data with a nonempty CM set
over `F`. -/
end IsogenyCount

namespace CMTorsor

open Elliptic_Curves Elliptic_Curves.Deuring

/-- Data for a CM torsor: an imaginary quadratic discriminant `D` and a prime power
`q` coprime to `|D|`. -/
structure CMTorsorData where
  D : ℤ
  hD : IsImagQuadDiscriminant D
  q : ℕ
  hq : 1 < q
  hcop : Nat.Coprime q D.natAbs

/-- Predicate that an ideal class in the class group of an order is represented by
an ideal of norm equal to a given prime `ℓ`. -/
variable {C : CMTorsorData} {F : Type*} [Field F] [Fintype F] (T : CMTorsor C F)

end CMTorsor

end
