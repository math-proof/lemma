/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/SingerDifferenceSet.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3

Singer's cyclic difference-set theorem, via the classical projective-plane
argument: a 2-dimensional subspace of a degree-3 field extension picks out a
`(q + 1)`-element difference set in `ZMod (q ^ 2 + q + 1)`.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.SimpleRing.Basic

@[expose] public section

open scoped IntermediateField

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


namespace MetaMathlibExt

section SingerPrivate

variable {K L : Type*} [Field K] [Field L] [Fintype K] [Fintype L] [Algebra K L]

omit [Fintype K] [Fintype L] in
/-- The trace of `W` in `ZMod N`: indices `i` with `γ ^ i.val ∈ W`. -/
noncomputable def sgT (q : ℕ) (g : Lˣ) (W : Submodule K L) :
    Finset (ZMod (q ^ 2 + q + 1)) :=
  @Finset.filter _ (fun i => (g : L) ^ i.val ∈ W) (Classical.decPred _) Finset.univ

omit [Fintype K] in
/-- The elements of `L` lying in `W`, as a finset. -/
noncomputable def sgC (W : Submodule K L) : Finset L :=
  @Finset.filter _ (fun y => y ∈ W) (Classical.decPred _) Finset.univ

end SingerPrivate
end MetaMathlibExt
