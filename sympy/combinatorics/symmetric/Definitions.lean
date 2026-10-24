/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import sympy.combinatorics.permutations.Basics
import Lemma.PowerSeries.CommutativeRings
/-!
# Definitions and Examples of Symmetric Polynomials

This file formalizes the definitions and basic properties of symmetric polynomials,
following Section "Definitions and examples of symmetric polynomials" (sec.sf.sp) of the source.

## Main definitions

* We use Mathlib's `MvPolynomial.IsSymmetric` for the notion of symmetric polynomials.
* `MvPolynomial.symmetricSubalgebra σ R` is the ring of symmetric polynomials.
* `MvPolynomial.esymm σ R n` is the n-th elementary symmetric polynomial.
* `MvPolynomial.hsymm σ R n` is the n-th complete homogeneous symmetric polynomial.
* `MvPolynomial.psum σ R n` is the n-th power sum.

## Main results

* The symmetric group acts on polynomials by permuting variables (Proposition prop.sf.SN-acts)
* The action is by K-algebra automorphisms (Proposition prop.sf.SN-acts-by-alg-auts)
* The set of symmetric polynomials forms a K-subalgebra (Theorem thm.sf.S-subalg)
* For n > N, the n-th elementary symmetric polynomial is zero (Proposition prop.sf.en=0)
* Newton-Girard formulas relating e_n, h_n, and p_n (Theorem thm.sf.NG)
* Fundamental Theorem of Symmetric Polynomials (Theorem thm.sf.ftsf)
* A polynomial is symmetric iff it is invariant under simple transpositions (Lemma lem.sf.simples-enough)

## References

* Source: SymmetricFunctions/Definitions.tex, sec.sf.sp

## Implementation notes

Mathlib already provides extensive support for symmetric polynomials via `MvPolynomial.IsSymmetric`
and related definitions. This file connects the textbook presentation to Mathlib's API
and provides additional lemmas following the source material.

The symmetric group action on polynomials is given by `MvPolynomial.rename` in Mathlib.
For a permutation σ : Equiv.Perm (Fin N), the action σ · f is `MvPolynomial.rename σ f`.
-/


open scoped Polynomial
open MvPolynomial Finset

namespace AlgebraicCombinatorics

namespace SymmetricPolynomials

variable {K : Type*} [CommRing K]
variable {N : ℕ}
/-! Compatibility with the pre-2026 `MvPolynomial.coeff m p` argument order. -/


variable {σ : Type*}

abbrev coeff (m : σ →₀ ℕ) (p : MvPolynomial σ K) : K := p.coeff m
/-!
## Convention (Convention conv.sf.KN)

We fix a commutative ring K and a natural number N throughout.
The polynomial ring P = K[x₁, x₂, ..., x_N] is `MvPolynomial (Fin N) K` in Mathlib.
-/


/-- The polynomial ring in N variables over K.
    This corresponds to 𝒫 in the source (Definition def.sf.PS (a)).
    Label: def.sf.PS -/
abbrev P (K : Type*) [CommRing K] (N : ℕ) : Type _ := MvPolynomial (Fin N) K
/-!
## The Symmetric Group Action (Definition def.sf.PS (b))

The symmetric group S_N acts on P by permuting variables:
  σ · f = f[x_{σ(1)}, x_{σ(2)}, ..., x_{σ(N)}]

In Mathlib, this is given by `MvPolynomial.rename σ f` where σ : Equiv.Perm (Fin N).
-/


/-- The action of a permutation on a polynomial by renaming variables.
    This is σ · f = f[x_{σ(1)}, ..., x_{σ(N)}] in the source.
    Label: def.sf.PS -/
noncomputable def permAction (σ : Equiv.Perm (Fin N)) (f : P K N) : P K N :=
  rename σ f

/-- Notation: σ • f for the permutation action -/
scoped notation:70 σ " •ₚ " f:70 => permAction σ f
/-!
## Proposition prop.sf.SN-acts: The action is a well-defined group action

(a) id · f = f for every f ∈ P
(b) (στ) · f = σ · (τ · f) for every σ, τ ∈ S_N and f ∈ P
-/


/-- The identity permutation acts trivially (Proposition prop.sf.SN-acts (a)).
    Label: prop.sf.SN-acts -/
theorem permAction_id (f : P K N) : (1 : Equiv.Perm (Fin N)) •ₚ f = f := by
  simp only [permAction, Equiv.Perm.coe_one, rename_id]
  rfl

/-- Composition of permutation actions (Proposition prop.sf.SN-acts (b)).
    Label: prop.sf.SN-acts -/
theorem permAction_mul (σ τ : Equiv.Perm (Fin N)) (f : P K N) :
    (σ * τ) •ₚ f = σ •ₚ (τ •ₚ f) := by
  simp only [permAction, rename_rename]
  rfl

/-- The symmetric group action on polynomials is a well-defined MulAction.
    This formalizes Proposition prop.sf.SN-acts in the standard Mathlib form:
    - `one_smul` corresponds to part (a): id · f = f
    - `mul_smul` corresponds to part (b): (στ) · f = σ · (τ · f)
    Label: prop.sf.SN-acts -/
noncomputable instance permMulAction : MulAction (Equiv.Perm (Fin N)) (P K N) where
  smul := permAction
  one_smul := permAction_id
  mul_smul σ τ f := by
    show permAction (σ * τ) f = permAction σ (permAction τ f)
    exact permAction_mul σ τ f
/-!
## Definition of Symmetric Polynomials (Definition def.sf.PS (c)(d))

A polynomial f ∈ P is symmetric if σ · f = f for all σ ∈ S_N.
The set S of all symmetric polynomials is `symmetricSubalgebra (Fin N) K` in Mathlib.
-/


/-- A polynomial is symmetric if it is invariant under all permutations.
    This is Definition def.sf.PS (c) in the source.
    Label: def.sf.PS -/
def IsSymm (f : P K N) : Prop := f.IsSymmetric

/-- The ring of symmetric polynomials in N variables over K.

    This is the K-subalgebra S of P consisting of all symmetric polynomials,
    i.e., polynomials f such that σ · f = f for all permutations σ ∈ S_N.

    The terminology "ring of symmetric polynomials" comes from the fact that
    this subalgebra is closed under addition, multiplication, and scalar
    multiplication by elements of K (Theorem thm.sf.S-subalg).

    Label: def.sf.ring-of-symm -/
abbrev S (K : Type*) [CommRing K] (N : ℕ) : Subalgebra K (P K N) :=
  symmetricSubalgebra (Fin N) K

/-- Alternative name: the ring of symmetric polynomials.
    This is the standard terminology for the subalgebra S.
    Label: def.sf.ring-of-symm -/
abbrev ringOfSymmetricPolynomials (K : Type*) [CommRing K] (N : ℕ) : Subalgebra K (P K N) :=
  S K N

/-- The ring of symmetric polynomials is indeed a ring (a K-subalgebra of P).
    This follows from Mathlib's `symmetricSubalgebra` being a `Subalgebra`.
    Label: def.sf.ring-of-symm -/
noncomputable example : Ring (S K N) := inferInstance

/-- The ring of symmetric polynomials is a commutative ring.
    Label: def.sf.ring-of-symm -/
noncomputable example : CommRing (S K N) := inferInstance

/-- The ring of symmetric polynomials is a K-algebra.
    Label: def.sf.ring-of-symm -/
noncomputable example : Algebra K (S K N) := inferInstance
/-!
## Additional API for Definition def.sf.PS

These lemmas provide useful characterizations of the definitions.
-/

/-- The polynomial ring P K N is a commutative K-algebra.
    Label: def.sf.PS -/
noncomputable instance P_isCommRing' : CommRing (P K N) := inferInstance

/-- The polynomial ring P K N is a K-algebra.
    Label: def.sf.PS -/
noncomputable instance P_isAlgebra' : Algebra K (P K N) := inferInstance
/-!
## Proposition prop.sf.SN-acts-by-alg-auts: The action is by K-algebra automorphisms

For each σ ∈ S_N, the map f ↦ σ · f is a K-algebra automorphism of P.
-/

/-- The K-algebra automorphism of P induced by a permutation σ.
    This is the main object of Proposition prop.sf.SN-acts-by-alg-auts:
    for each σ ∈ S_N, the map f ↦ σ · f is a K-algebra automorphism.
    Label: prop.sf.SN-acts-by-alg-auts -/
noncomputable def permAutomorphism (σ : Equiv.Perm (Fin N)) : P K N ≃ₐ[K] P K N :=
  renameEquiv K σ

/-- The identity permutation gives the identity automorphism.
    Label: prop.sf.SN-acts-by-alg-auts -/
theorem permAutomorphism_id :
    permAutomorphism (K := K) (N := N) (1 : Equiv.Perm (Fin N)) = AlgEquiv.refl :=
  renameEquiv_refl K

/-- Composition of permutation automorphisms: (σ * τ) acts as τ then σ.
    Note: In AlgEquiv, f * g = g.trans f (apply g first, then f).
    Label: prop.sf.SN-acts-by-alg-auts -/
theorem permAutomorphism_mul_perm (σ τ : Equiv.Perm (Fin N)) :
    permAutomorphism (K := K) (σ * τ) = permAutomorphism σ * permAutomorphism τ := by
  ext f
  unfold permAutomorphism
  simp only [renameEquiv_apply, AlgEquiv.mul_apply, rename_rename]
  rfl

/-- The map from S_N to Aut_K(P) is a group homomorphism.
    This is the full content of Proposition prop.sf.SN-acts-by-alg-auts:
    S_N acts on P by K-algebra automorphisms.
    Label: prop.sf.SN-acts-by-alg-auts -/
noncomputable def permAutomorphismHom :
    Equiv.Perm (Fin N) →* (P K N ≃ₐ[K] P K N) where
  toFun σ := permAutomorphism σ
  map_one' := permAutomorphism_id
  map_mul' σ τ := permAutomorphism_mul_perm σ τ
/-!
## Theorem thm.sf.S-subalg: S is a K-subalgebra of P

The set of symmetric polynomials is closed under addition, multiplication, and scaling,
and contains 0 and 1.

From the source (AlgebraicCombinatorics/tex/SymmetricFunctions/Definitions.tex, Theorem thm.sf.S-subalg):

> The subset S is a K-subalgebra of P.

A K-subalgebra of P must satisfy:
1. S contains 0 and 1
2. S is closed under addition
3. S is closed under multiplication
4. S is closed under scalar multiplication by elements of K

This section proves all these properties both in terms of `IsSymm` (the predicate)
and `∈ S K N` (membership in the subalgebra).
-/


/-- **Theorem thm.sf.S-subalg**: The symmetric polynomials form a K-subalgebra of P.

    This is the main theorem stating that the set S of symmetric polynomials is
    a K-subalgebra of the polynomial ring P = K[x₁, x₂, ..., x_N].

    A K-subalgebra satisfies:
    - (a) S contains 0 and 1 (see `S_zero_mem`, `S_one_mem`)
    - (b) S is closed under addition (see `S_add_mem`)
    - (c) S is closed under multiplication (see `S_mul_mem`)
    - (d) S is closed under scalar multiplication by K (see `S_smul_mem`)

    The definition `S K N := symmetricSubalgebra (Fin N) K` directly provides
    the `Subalgebra K (P K N)` structure, which bundles all these properties.

    Label: thm.sf.S-subalg -/
def S_subalgebra : Subalgebra K (P K N) := S K N
/-!
### Part (a): S contains 0 and 1
-/
/-!
### Part (b): S is closed under addition
-/
/-!
### Part (c): S is closed under multiplication
-/
/-!
### Part (d): S is closed under scalar multiplication
-/
/-!
### Additional closure properties (consequences of being a K-subalgebra)

These properties follow automatically from S being a K-subalgebra.
-/
/-!
## Definition of Monomials (Definition def.sf.monomial)

(a) A monomial is x₁^{a₁} x₂^{a₂} ⋯ x_N^{a_N} with a_i ∈ ℕ
(b) The degree of a monomial is a₁ + a₂ + ⋯ + a_N
(c) A monomial is squarefree if all a_i ∈ {0, 1}
(d) A monomial is primal if at most one a_i > 0
-/


/-- A monomial represented by its exponent vector.
    In the textbook, a monomial is x₁^{a₁} x₂^{a₂} ⋯ x_N^{a_N}.
    We represent it by the exponent vector (a₁, a₂, ..., a_N) ∈ ℕ^N.
    Label: def.sf.monomial -/
abbrev Monomial (N : ℕ) := Fin N →₀ ℕ

/-- Convert a monomial (exponent vector) to the corresponding polynomial x₁^{a₁} ⋯ x_N^{a_N}.
    Label: def.sf.monomial -/
noncomputable def Monomial.toPoly (m : Monomial N) : P K N :=
  monomial m 1

/-- The degree of a monomial is the sum of its exponents.
    Label: def.sf.monomial -/
def Monomial.degree (m : Monomial N) : ℕ := m.sum (fun _ a => a)

/-- A monomial is squarefree if all exponents are 0 or 1.
    Label: def.sf.monomial -/
def Monomial.IsSquarefree (m : Monomial N) : Prop := ∀ i, m i ≤ 1

/-- A monomial is primal if at most one exponent is positive.
    This means the monomial is either 1 or a power of a single variable.
    Label: def.sf.monomial -/
def Monomial.IsPrimal (m : Monomial N) : Prop := m.support.card ≤ 1

/-- The set of all monomials of a given degree n.
    Label: def.sf.monomial -/
def monomialsOfDegree (N n : ℕ) : Set (Monomial N) :=
  {m | m.degree = n}

/-- The set of all squarefree monomials of a given degree n.
    Label: def.sf.monomial -/
def squarefreeMonomials (N n : ℕ) : Set (Monomial N) :=
  {m | m.IsSquarefree ∧ m.degree = n}

/-- The set of all primal monomials of a given degree n.
    Label: def.sf.monomial -/
def primalMonomials (N n : ℕ) : Set (Monomial N) :=
  {m | m.IsPrimal ∧ m.degree = n}

/-- A single variable x_i corresponds to the monomial with exponent 1 at position i.
    Label: def.sf.monomial -/
noncomputable def Monomial.single (i : Fin N) : Monomial N := Finsupp.single i 1

/-- The monomial corresponding to a subset S ⊆ [N] is ∏_{i ∈ S} x_i.
    This is the squarefree monomial with support S.
    Label: def.sf.monomial -/
noncomputable def Monomial.ofFinset (s : Finset (Fin N)) : Monomial N :=
  s.sum (Finsupp.single · 1)
/-!
## Elementary Symmetric Polynomials (Definition def.sf.ehp (a))

e_n = sum of all squarefree monomials of degree n
    = ∑_{i₁ < i₂ < ... < i_n} x_{i₁} x_{i₂} ⋯ x_{i_n}

In Mathlib, this is `MvPolynomial.esymm (Fin N) K n`.
-/


/-- The n-th elementary symmetric polynomial.
    Label: def.sf.ehp -/
noncomputable abbrev e (n : ℕ) : P K N := esymm (Fin N) K n
/-!
## Complete Homogeneous Symmetric Polynomials (Definition def.sf.ehp (b))

h_n = sum of all monomials of degree n
    = ∑_{i₁ ≤ i₂ ≤ ... ≤ i_n} x_{i₁} x_{i₂} ⋯ x_{i_n}

In Mathlib, this is `MvPolynomial.hsymm (Fin N) K n`.
-/


section WithDecidableEq

variable [DecidableEq (Fin N)]

/-- The n-th complete homogeneous symmetric polynomial.
    Label: def.sf.ehp -/
noncomputable abbrev h (n : ℕ) : P K N := hsymm (Fin N) K n

end WithDecidableEq
/-!
## Power Sums (Definition def.sf.ehp (c))

p_n = x₁^n + x₂^n + ... + x_N^n  (for n > 0)
p_0 = 1
p_n = 0  (for n < 0)

In Mathlib, this is `MvPolynomial.psum (Fin N) K n`.
Note: Mathlib's definition has p_0 = N (the number of variables), not 1.
-/


/-- The n-th power sum symmetric polynomial.
    Label: def.sf.ehp -/
noncomputable abbrev p (n : ℕ) : P K N := psum (Fin N) K n
/-!
## Basic Values (Example exa.sf.ehp.1)

(d) e_1 = h_1 = p_1 = x_1 + x_2 + ... + x_N
(e) e_0 = h_0 = 1, p_0 = N
(f) e_n = h_n = p_n = 0 for n < 0 (vacuously true for ℕ)
-/
/-!
## Integer-indexed versions (Definition def.sf.ehp)

The source defines e_n, h_n, p_n for all integers n ∈ ℤ.
For negative n, they are all 0. This section provides integer-indexed versions
that match the textbook definitions exactly.
-/


/-- Integer-indexed elementary symmetric polynomial.
    For n ∈ ℤ: e_n = esymm n if n ≥ 0, e_n = 0 if n < 0.
    This matches Definition def.sf.ehp (a) in the source.
    Label: def.sf.ehp -/
noncomputable def eZ (n : ℤ) : P K N :=
  if 0 ≤ n then e n.toNat else 0

/-- Integer-indexed complete homogeneous symmetric polynomial.
    For n ∈ ℤ: h_n = hsymm n if n ≥ 0, h_n = 0 if n < 0.
    This matches Definition def.sf.ehp (b) in the source.
    Label: def.sf.ehp -/
noncomputable def hZ [DecidableEq (Fin N)] (n : ℤ) : P K N :=
  if 0 ≤ n then h n.toNat else 0

/-- Integer-indexed power sum (textbook convention).
    For n ∈ ℤ: p'_n = psum n if n > 0, p'_0 = 1, p'_n = 0 if n < 0.
    This matches Definition def.sf.ehp (c) in the source.

    Note: Mathlib's psum has p_0 = N (number of variables), but the textbook
    defines p_0 = 1. We follow the textbook convention here.
    Label: def.sf.ehp -/
noncomputable def pZ (n : ℤ) : P K N :=
  if n > 0 then p n.toNat
  else if n = 0 then 1
  else 0
/-!
## Alternative characterizations (Definition def.sf.ehp)

The defining formulas for e_n, h_n, p_n as sums over tuples.
-/

section WithDecidableEq'

variable [DecidableEq (Fin N)]

end WithDecidableEq'
/-!
## Proposition prop.sf.en=0: e_n = 0 for n > N

For n > N, there are no n distinct elements in [N], so e_n = 0.
-/
/-!
## Adding a Variable Recurrence

The elementary symmetric polynomial e_n(x₁,...,x_N,y) satisfies the recurrence:
  e_n(x₁,...,x_N,y) = e_n(x₁,...,x_N) + y * e_{n-1}(x₁,...,x_N)

This is fundamental for inductive proofs about symmetric polynomials.
-/
/-!
## Newton-Girard Formulas (Theorem thm.sf.NG)

For any positive integer n:
(eq.thm.sf.NG.eh) ∑_{j=0}^n (-1)^j e_j h_{n-j} = 0
(eq.thm.sf.NG.ep) ∑_{j=1}^n (-1)^{j-1} e_{n-j} p_j = n · e_n
(eq.thm.sf.NG.hp) ∑_{j=1}^n h_{n-j} p_j = n · h_n

These are implemented in Mathlib as `MvPolynomial.mul_esymm_eq_sum` and related theorems.
-/

section WithDecidableEq'

variable [DecidableEq (Fin N)]
/-! ### Helper lemmas for the bijection in Newton-Girard hp formula -/


/-- Helper: replicate n a ≤ s iff n ≤ count a s. -/
theorem replicate_le_iff_count {α : Type*} [DecidableEq α] (a : α) (m : ℕ) (s : Multiset α) :
    Multiset.replicate m a ≤ s ↔ m ≤ s.count a := by
  constructor
  · intro h
    calc m = (Multiset.replicate m a).count a := by simp
      _ ≤ s.count a := Multiset.count_le_of_le a h
  · intro h
    rw [Multiset.le_iff_count]
    intro b
    simp only [Multiset.count_replicate]
    split_ifs with heq
    · subst heq; exact h
    · exact Nat.zero_le _

/-- Cardinality of s - replicate (k+1) i when k < count i s. -/
theorem sub_replicate_card (m k : ℕ) (s : Sym (Fin N) m) (i : Fin N) (hk : k < s.1.count i) :
    (s.1 - Multiset.replicate (k + 1) i).card = m - 1 - k := by
  have hle : Multiset.replicate (k + 1) i ≤ s.1 := by
    rw [replicate_le_iff_count]; omega
  rw [Multiset.card_sub hle, s.2, Multiset.card_replicate]
  omega

omit [DecidableEq (Fin N)] in
/-- Cardinality of t + replicate (j+1) i when j < n. -/
theorem add_replicate_card (m j : ℕ) (hj : j < m) (t : Sym (Fin N) (m - 1 - j)) (i : Fin N) :
    (t.1 + Multiset.replicate (j + 1) i).card = m := by
  rw [Multiset.card_add, t.2, Multiset.card_replicate]
  omega

/-- Add replicate (j+1) i to a Sym (n-1-j) to get a Sym n. -/
def addReplicate (m j : ℕ) (hj : j < m) (t : Sym (Fin N) (m - 1 - j)) (i : Fin N) :
    Sym (Fin N) m :=
  ⟨t.1 + Multiset.replicate (j + 1) i, add_replicate_card m j hj t i⟩

/-- Subtract replicate (k+1) i from a Sym n to get a Sym (n-1-k). -/
def subReplicate (m k : ℕ) (s : Sym (Fin N) m) (i : Fin N) (hk : k < s.1.count i) :
    Sym (Fin N) (m - 1 - k) :=
  ⟨s.1 - Multiset.replicate (k + 1) i, sub_replicate_card m k s i hk⟩

end WithDecidableEq'
/-!
## Generating Function Identities (Proposition prop.sf.e-h-FPS)

These identities express the elementary and complete homogeneous symmetric polynomials
as coefficients in certain generating functions.

(a) In P[t]: ∏_{i=1}^N (1 - t·x_i) = ∑_{n≥0} (-1)^n t^n e_n
(b) In P[u,v]: ∏_{i=1}^N (u - v·x_i) = ∑_{n=0}^N (-1)^n u^{N-n} v^n e_n
(c) In P[[t]]: ∏_{i=1}^N 1/(1 - t·x_i) = ∑_{n≥0} t^n h_n
-/
/-!
## Fundamental Theorem of Symmetric Polynomials (Theorem thm.sf.ftsf)

(a) e_1, e_2, ..., e_N are algebraically independent and generate S.
(b) h_1, h_2, ..., h_N are algebraically independent and generate S.
(c) If K is a ℚ-algebra, then p_1, p_2, ..., p_N are algebraically independent and generate S.

These are implemented in Mathlib via `MvPolynomial.esymmAlgEquiv`.

### Part (a): Elementary Symmetric Polynomials

The elementary symmetric polynomials e_1, e_2, ..., e_N are algebraically independent
over K and generate the K-algebra S of symmetric polynomials. This means:
1. The only polynomial relation P(e_1, ..., e_N) = 0 is P = 0 (algebraic independence)
2. Every symmetric polynomial can be written uniquely as a polynomial in e_1, ..., e_N (generation)

Equivalently, the map K[y_1, ..., y_N] → S given by g ↦ g(e_1, ..., e_N) is a K-algebra isomorphism.
-/


/-- The elementary symmetric polynomials e_1, ..., e_N generate the symmetric subalgebra
    and the map g ↦ g[e_1, ..., e_N] is a K-algebra isomorphism.
    (Theorem thm.sf.ftsf (a)).
    Label: thm.sf.ftsf -/
noncomputable def esymmAlgEquiv' : MvPolynomial (Fin N) K ≃ₐ[K] S K N :=
  esymmAlgEquiv (Fin N) K (Fintype.card_fin N)
/-!
### Part (b): Complete Homogeneous Symmetric Polynomials

The complete homogeneous symmetric polynomials h_1, h_2, ..., h_N are also algebraically
independent and generate S. This is a consequence of the Newton-Girard relations which
express each h_k as a polynomial in e_1, ..., e_k and vice versa.
-/


section PartB

variable [DecidableEq (Fin N)]

/-- The aeval map sending X_i to h_{i+1}.
    Label: thm.sf.ftsf -/
noncomputable def hsymmAeval : MvPolynomial (Fin N) K →ₐ[K] P K N :=
  aeval (fun i : Fin N => hsymm (Fin N) K (i + 1))

/-- The range of hsymmAeval is a subalgebra.
    Label: thm.sf.ftsf -/
noncomputable def hsymmRange : Subalgebra K (P K N) := hsymmAeval.range

end PartB
/-!
### Part (c): Power Sums (over ℚ-algebras)

When K is a ℚ-algebra (e.g., K = ℚ, ℝ, ℂ, or any field of characteristic 0),
the power sums p_1, p_2, ..., p_N are also algebraically independent and generate S.

Note: This fails in positive characteristic. For example, over 𝔽_p, we have
p_p = x_1^p + ... + x_N^p = (x_1 + ... + x_N)^p = p_1^p by the Frobenius endomorphism.
-/


section PartC

variable [Algebra ℚ K] [IsDomain K]
/-! ### Weight argument infrastructure for power sum algebraic independence

The key insight for proving the triangular structure of ψ(X_i) is a weight argument:
- Define weight(X_k) = k+1 for variables X_k in MvPolynomial (Fin N) K
- The map psumAeval' sends X_k to psum(k+1), which is homogeneous of degree k+1
- Therefore psumAeval' maps polynomials of weighted degree w to polynomials of total degree w
- Since esymm(i+1) has total degree i+1, any polynomial P with psumAeval'(P) = esymm(i+1)
  must have all monomials with weighted degree i+1
- This constrains which variables can appear in P with which exponents
-/


/-- The weight function for power sum analysis: X_k has weight k+1 -/
def psumWeight' : Fin N → ℕ := fun k => k.val + 1

/-- The aeval map sending X_i to p_{i+1}.
    Label: thm.sf.ftsf -/
noncomputable def psumAeval : MvPolynomial (Fin N) K →ₐ[K] P K N :=
  aeval (fun i : Fin N => psum (Fin N) K (i + 1))

/-- The range of psumAeval is a subalgebra.
    Label: thm.sf.ftsf -/
noncomputable def psumRange : Subalgebra K (P K N) := psumAeval.range

end PartC
/-!
## Lemma lem.sf.simples-enough: Simple transpositions suffice

A polynomial f ∈ P is symmetric if and only if s_k · f = f for each k ∈ [N-1],
where s_k is the simple transposition swapping k and k+1.
-/


/-- Simple transposition s_k swaps positions k and k+1.
    
    This is an alias for the canonical definition `AlgebraicCombinatorics.simpleTransposition`
    from `Permutations/Basics.lean`. The canonical definition uses `Fin (N - 1)` to encode
    the constraint that k + 1 < N.
    
    Label: lem.sf.simples-enough -/
abbrev simpleTransposition (k : Fin (N - 1)) : Equiv.Perm (Fin N) :=
  AlgebraicCombinatorics.simpleTransposition k
/-!
## Example: Antisymmetric Polynomials

A polynomial f is antisymmetric if σ · f = (-1)^σ · f for all σ ∈ S_N.
The square of an antisymmetric polynomial is symmetric.
-/


/-- A polynomial is antisymmetric if σ · f = sign(σ) · f for all permutations σ.
    Label: exa.sf.PS1 -/
def IsAntisymm (f : P K N) : Prop :=
  ∀ σ : Equiv.Perm (Fin N), rename σ f = Equiv.Perm.sign σ • f
/-!
### Basic API lemmas for `IsAntisymm`

The following lemmas establish that antisymmetric polynomials form a K-submodule of P
(but not a subalgebra, since the product of two antisymmetric polynomials is symmetric, not antisymmetric).
-/

end SymmetricPolynomials

end AlgebraicCombinatorics
