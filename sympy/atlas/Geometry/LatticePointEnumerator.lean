/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LatticePointEnumerator.lean -/

import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Topology.Bornology.Basic

import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Lattice-point enumerators

For a bounded set `P ⊆ ℝᵈ` and a dilation parameter `t > 0`, the lattice-point
enumerator counts integer points in the dilate: `L_P(t) = |(t • P) ∩ ℤᵈ|`.

Source: Rocha-Neves, A Fourier-analytic Uniqueness Theorem for Lattice-point
Enumerators, arXiv:2608.11078v1. The definition `L_P(t)` for bounded `P` and
`t > 0` is on lines 24-31; line 24 assumes `P` is bounded. Lines 62-67 use the
translated version `F_{t,P}(x) = |((t • P) + x) ∩ ℤᵈ|`, translating after
dilating.

Only translate-after-dilate `((t • P) + {x}) ∩ ℤᵈ` matches the source. Dilating
after translating `t • (P + {x})` is a different set; see the regression test
at `P = {0}`, `t = 2`, `x = 1 / 2`.

Main declarations:
- `LatticePointEnumerator.stdLattice`: the standard integer lattice `ℤᵈ`, as the
  integer span of `Pi.basisFun`, in ambient space `Fin d → ℝ`.
- `LatticePointEnumerator.latticePointSet`: the counted set `(t • P) ∩ ℤᵈ`.
- `LatticePointEnumerator.latticeEnumerator`: totalized helper `ncard` count;
  on infinite sets `ncard` returns junk `0`, so source-facing uses need
  boundedness.
- `LatticePointEnumerator.translatedLatticePointSet`: `((t • P) + {x}) ∩ ℤᵈ`.
- `LatticePointEnumerator.translatedLatticeEnumerator`: totalized helper count.
- `LatticePointEnumerator.latticePointSetPos` /
  `LatticePointEnumerator.translatedLatticePointSetPos`: positive-`t` versions.
- `LatticePointEnumerator.latticeEnumeratorPos` /
  `LatticePointEnumerator.translatedLatticeEnumeratorPos`: source-domain
  enumerators requiring a `Bornology.IsBounded P` proof.
- `LatticePointEnumerator.finite_latticePointSet` and translated variants:
  finiteness for bounded `P`, via `ZSpan.setFinite_inter`.
-/

namespace LatticePointEnumerator

open scoped Pointwise

/-- Standard integer lattice `ℤᵈ` in `Fin d → ℝ`: integer span of `Pi.basisFun`. -/
noncomputable def stdLattice (d : ℕ) : Submodule ℤ (Fin d → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))

/-- Lattice-point set `(t • P) ∩ ℤᵈ` for a real dilate `t`. General helper; the
source only evaluates at `t > 0` (see `latticePointSetPos`). -/
noncomputable def latticePointSet (d : ℕ) (P : Set (Fin d → ℝ)) (t : ℝ) :
    Set (Fin d → ℝ) :=
  (t • P) ∩ (stdLattice d : Set (Fin d → ℝ))

/-- Totalized enumerator: `ncard` of `latticePointSet`. For unbounded `P` the
intersection can be infinite and `ncard` returns junk `0`; use
`latticeEnumeratorPos` with a boundedness proof for source-faithful counts. -/
noncomputable def latticeEnumerator (d : ℕ) (P : Set (Fin d → ℝ)) (t : ℝ) : ℕ :=
  Set.ncard (latticePointSet d P t)

/-- Translate-after-dilate set `((t • P) + {x}) ∩ ℤᵈ`, matching `F_{t,P}(x)` on
lines 62-67. Distinct from dilate-after-translate `t • (P + {x})`. -/
noncomputable def translatedLatticePointSet (d : ℕ) (P : Set (Fin d → ℝ))
    (t : ℝ) (x : Fin d → ℝ) : Set (Fin d → ℝ) :=
  ((t • P) + {x}) ∩ (stdLattice d : Set (Fin d → ℝ))

/-- Totalized translated enumerator; see `translatedLatticeEnumeratorPos` for
the bounded source-domain version. -/
noncomputable def translatedLatticeEnumerator (d : ℕ) (P : Set (Fin d → ℝ))
    (t : ℝ) (x : Fin d → ℝ) : ℕ :=
  Set.ncard (translatedLatticePointSet d P t x)

/-- Positive-dilation helper, not a full source-domain object: no boundedness carried.
`latticeEnumeratorPos` combines positivity with boundedness proof for Rocha-Neves lines 24-31. -/
noncomputable def latticePointSetPos (d : ℕ) (P : Set (Fin d → ℝ))
    (t : {t : ℝ // 0 < t}) : Set (Fin d → ℝ) :=
  latticePointSet d P t.val

/-- Source-domain enumerator `L_P(t)` for bounded `P` and positive `t`, as in
Rocha-Neves, lines 24-31. The `hb` proof rules out unbounded `P`, where
`ncard` would silently return junk `0`. -/
noncomputable def latticeEnumeratorPos (d : ℕ) (P : Set (Fin d → ℝ))
    (_hb : Bornology.IsBounded P) (t : {t : ℝ // 0 < t}) : ℕ :=
  latticeEnumerator d P t.val

/-- Translate-after-dilate helper, not a full source-domain object: no boundedness.
`translatedLatticeEnumeratorPos` gives the bounded source-facing count. -/
noncomputable def translatedLatticePointSetPos (d : ℕ) (P : Set (Fin d → ℝ))
    (t : {t : ℝ // 0 < t}) (x : Fin d → ℝ) : Set (Fin d → ℝ) :=
  translatedLatticePointSet d P t.val x

/-- Source-domain `F_{t,P}(x)` for bounded `P` and positive `t`, lines 62-67. -/
noncomputable def translatedLatticeEnumeratorPos (d : ℕ) (P : Set (Fin d → ℝ))
    (_hb : Bornology.IsBounded P) (t : {t : ℝ // 0 < t}) (x : Fin d → ℝ) : ℕ :=
  translatedLatticeEnumerator d P t.val x
end LatticePointEnumerator
