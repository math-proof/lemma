-- Carved from Lemma/Definitions/Def_Compat_Mathlib430.lean: instance decls only.
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
import Lemma.Compat.Mathlib430

set_option autoImplicit false

/-! ## Block A — Mathlib v4.30.0 Mathlib/RepresentationTheory/Basic.lean:391-419 (section MulAction), names suffixed `Finsupp` -/


/-! ## Block C — Mathlib v4.30.0 Mathlib/RepresentationTheory/Rep/Basic.lean:336-346 and 404-412, names suffixed `Finsupp` -/


/-! ## Block D — AddAut: Mathlib v4.30.0 Mathlib/Algebra/Group/End.lean:746-801 (+ GroupWithZero/Action/Basic.lean:89-92 and :104-112, Ring/AddAut.lean:32), lemma names primed -/

namespace AddAut

section Compat430

variable (A : Type*) [Add A]

instance : Group (AddAut A) where
  mul g h := AddEquiv.trans h g
  one := AddEquiv.refl _
  inv := AddEquiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel := AddEquiv.self_trans_symm

/- The following thirteen lemmas are Mathlib v4.30.0 `Mathlib/Algebra/Group/End.lean:758-801`
verbatim except that each name carries a trailing prime. -/

end Compat430

end AddAut

namespace AddAut
instance applyDistribMulAction' {A : Type*} [AddMonoid A] : DistribMulAction (AddAut A) A where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero := AddEquiv.map_zero
  smul_add := AddEquiv.map_add

instance apply_faithfulSMul' {A : Type*} [AddMonoid A] : FaithfulSMul (AddAut A) A :=
  ⟨fun h => AddEquiv.ext h⟩
end AddAut

/-! ## Block E — elliptic (divisibility) sequence predicates: Mathlib v4.30.0
Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:78-110 (verbatim; names primed). Vendored because Mathlib v4.33.0 (db584cd6,
same file :286-295) RENAMED AND REDEFINED them (`IsEllipticSequence W := ∀ p q r, IsEllipticNet.rel W p q r 0 = 0`,
`IsDvdSequence` over ℤ instead of ℕ) and kept the 4.30 names only as deprecated aliases of the NEW predicates. -/


/-! ## Block G — ramification/inertia cardinality lemmas under the separability hypothesis (adapted from Mathlib v4.30.0,
Mathlib/NumberTheory/RamificationInertia/Galois.lean; v4.33.0 restates them assuming PerfectField of the residue field). Theorems only,
primed names; no definitions involved. -/

