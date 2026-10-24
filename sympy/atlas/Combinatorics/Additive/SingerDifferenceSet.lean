/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/SingerDifferenceSet.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3

Singer's cyclic difference-set theorem, via the classical projective-plane
argument: a 2-dimensional subspace of a degree-3 field extension picks out a
`(q + 1)`-element difference set in `ZMod (q ^ 2 + q + 1)`.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.FieldTheory.Finiteness
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Singer's cyclic difference-set theorem

Source: Harri Haanpää, *Minimum Sum and Difference Covers of Abelian Groups*,
Journal of Integer Sequences 7 (2004), Article 04.2.6,
<https://cs.uwaterloo.ca/journals/JIS/VOL7/Haanpaa/haanpaa.tex>,
difference-set definition and Singer prime-power construction, lines 209–215.

For `q` a prime power, there is a `(q + 1)`-element subset `D` of the cyclic
group `ZMod (q ^ 2 + q + 1)` in which every nonzero element is uniquely an
ordered difference of two members of `D`, via the classical projective-plane
argument over the degree-3 extension of the field with `q` elements.
-/

open scoped IntermediateField

namespace MetaMathlibExt

section SingerPrivate

variable {K L : Type*} [Field K] [Field L] [Fintype K] [Fintype L] [Algebra K L]

omit [Fintype K] [Fintype L] in
/-- The trace of `W` in `ZMod N`: indices `i` with `γ ^ i.val ∈ W`. -/
private noncomputable def sgT (q : ℕ) (g : Lˣ) (W : Submodule K L) :
    Finset (ZMod (q ^ 2 + q + 1)) :=
  @Finset.filter _ (fun i => (g : L) ^ i.val ∈ W) (Classical.decPred _) Finset.univ

omit [Fintype K] in
/-- The elements of `L` lying in `W`, as a finset. -/
private noncomputable def sgC (W : Submodule K L) : Finset L :=
  @Finset.filter _ (fun y => y ∈ W) (Classical.decPred _) Finset.univ
end SingerPrivate
end MetaMathlibExt
