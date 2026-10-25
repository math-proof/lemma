/-
Copyright: the vendored blocks below are verbatim copies from Mathlib (Apache-2.0; see Mathlib's LICENSE),
release v4.30.0 = leanprover-community/mathlib4 commit c5ea00351c28e24afc9f0f84379aa41082b1188f, with declarations
RENAMED (suffix `Finsupp` / trailing prime) so they do not clash with Mathlib v4.33.0. Bodies are the Mathlib v4.30.0 text
with its docstrings omitted, otherwise byte-identical unless a line is marked `-- [port]`.
-/
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.GroupWithZero.Action.Basic
import Mathlib.Algebra.Ring.AddAut
import Mathlib.Algebra.Ring.Action.Submonoid
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Notation.Algebra.Ring.Action.Submonoid

set_option autoImplicit false

/-! ## Block A — Mathlib v4.30.0 Mathlib/RepresentationTheory/Basic.lean:391-419 (section MulAction), names suffixed `Finsupp` -/

namespace Representation

section MulAction

variable (k : Type*) [Semiring k] (G : Type*) [Monoid G] (H : Type*) [MulAction G H]

end MulAction

/-! ## Block B — Mathlib v4.30.0 Mathlib/RepresentationTheory/Basic.lean:472-483 (section Group) -/

section Group

variable {k G V : Type*} [Semiring k] [Group G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V)

end Group

section Bridge

variable (k : Type*) [Semiring k] (G : Type*) [Monoid G] (H : Type*) [MulAction G H]

end Bridge

end Representation

/-! ## Block C — Mathlib v4.30.0 Mathlib/RepresentationTheory/Rep/Basic.lean:336-346 and 404-412, names suffixed `Finsupp` -/

namespace Rep

open CategoryTheory

universe w' u v

variable {k : Type u} {G : Type v} [Ring k] [Monoid G]

section

variable (k G)

noncomputable abbrev ofMulActionFinsupp (H : Type w') [MulAction G H] : Rep k G := -- [port] `noncomputable` added (4.30 file had a noncomputable section)
  of <| Representation.ofMulActionFinsupp k G H

end

end Rep

/-! ## Block D — AddAut: Mathlib v4.30.0 Mathlib/Algebra/Group/End.lean:746-801 (+ GroupWithZero/Action/Basic.lean:89-92 and :104-112, Ring/AddAut.lean:32), lemma names primed -/

namespace AddAut

section Compat430

variable (A : Type*) [Add A]

end Compat430

end AddAut

namespace AddAut

end AddAut

/-! ## Block E — elliptic (divisibility) sequence predicates: Mathlib v4.30.0
Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:78-110 (verbatim; names primed). Vendored because Mathlib v4.33.0 (db584cd6,
same file :286-295) RENAMED AND REDEFINED them (`IsEllipticSequence W := ∀ p q r, IsEllipticNet.rel W p q r 0 = 0`,
`IsDvdSequence` over ℤ instead of ℕ) and kept the 4.30 names only as deprecated aliases of the NEW predicates. -/

section IsEllDivSequence430

universe u

variable {R : Type u} [CommRing R]

variable (W : ℤ → R)

end IsEllDivSequence430


/-! ## Block G — ramification/inertia cardinality lemmas under the separability hypothesis (adapted from Mathlib v4.30.0,
Mathlib/NumberTheory/RamificationInertia/Galois.lean; v4.33.0 restates them assuming PerfectField of the residue field). Theorems only,
primed names; no definitions involved. -/

namespace Ideal

section inertia430

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
  [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]

open scoped Pointwise


attribute [local instance] Ideal.Quotient.field in

end inertia430

end Ideal
