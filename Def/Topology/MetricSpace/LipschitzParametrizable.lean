/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/LipschitzParametrizable.lean -/

import Mathlib.Data.Set.Finite.Basic
import Mathlib.Topology.MetricSpace.Lipschitz


/-!
# N384 (Definition 19.4): Lipschitz parametrizable sets

Clean-room formalization of ATLAS `NumberTheoryI` N384, Definition 19.4:
a set `B` in a metric space `X` is `d`-Lipschitz parametrizable when it is
the union of the images of finitely many Lipschitz continuous maps
`fᵢ : [0, 1]^d → X`.

Here `[0, 1]^d` is the subtype of `Set.Icc (0 : Fin d → ℝ) 1`, and the
finite family is indexed by `Fin n`, with equality (not just covering).

## N386 supporting-source map

Supporting source (prerequisite only, not the full N386 theorem):
`Atlas/NumberTheoryI/code/AnalyticClassNumber.lean` at revision
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`, lines 49--62
(`IsLipschitzParametrizable.image_linearEquiv`).
That source shows the image of a parametrizable set under a linear
equivalence is parametrizable by composing charts; the general theorem
`IsLipschitzParametrizable.image_lipschitzWith` below abstracts this to an
arbitrary Lipschitz map, which is all the N386 change of basis needs.
-/

/-- The closed unit cube `[0, 1]^d`, as a set in `Fin d → ℝ`. -/
def unitCube (d : ℕ) : Set (Fin d → ℝ) :=
  Set.Icc 0 1

/-- A set `B` is `d`-Lipschitz parametrizable if it equals the union of the
ranges of finitely many Lipschitz maps out of the unit cube. -/
def IsLipschitzParametrizable {X : Type*} [MetricSpace X] (d : ℕ) (B : Set X) : Prop :=
  ∃ (n : ℕ) (f : Fin n → (↥(unitCube d) → X)),
    (∀ i, ∃ K : NNReal, LipschitzWith K (f i)) ∧ B = ⋃ i, Set.range (f i)

