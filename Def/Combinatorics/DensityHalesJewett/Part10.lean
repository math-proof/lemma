/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DensityHalesJewett.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Combinatorics.HalesJewett
import Mathlib.Basic.Real.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
import Theorem.Combinatorics.DensityHalesJewett.Part8
/-! Proves the density Hales–Jewett theorem and the Graham–Rothschild theorem for lines. -/


namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

open scoped Finset

end MathlibExt.Combinatorics.DensityHalesJewettWanted

namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

noncomputable def dhjFiber {X I : Type*} [Fintype X]
    (Q : Finset X) (f : X → I) (i : I) : Finset X := by
  classical
  exact Q.filter fun x => f x = i

noncomputable def dhjBadIndices {k : ℕ} {ι : Type*} [Fintype ι]
    (B : Finset (ι → Fin (k + 1))) (x : ι → Fin (k + 1)) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun i => x ∉ dhjInsensitivePreimage B i

noncomputable def dhjFirstBad {k : ℕ} {ι : Type*} [Fintype ι]
    (i₀ : Fin k) (B : Finset (ι → Fin (k + 1))) (x : ι → Fin (k + 1)) : Fin k :=
  if h : (dhjBadIndices B x).Nonempty then (dhjBadIndices B x).min' h else i₀

noncomputable def dhjCell {k : ℕ} {ι : Type*} [Fintype ι]
    (B : Finset (ι → Fin (k + 1))) (i : Fin k) : Finset (ι → Fin (k + 1)) := by
  classical
  exact Finset.univ.filter fun x =>
    x ∉ dhjInsensitivePreimage B i ∧
      ∀ j : Fin k, j < i → x ∈ dhjInsensitivePreimage B j

noncomputable def dhjCellFactor {k : ℕ} {ι : Type*} [Fintype ι]
    [Fintype (ι → Fin (k + 1))] (B : Finset (ι → Fin (k + 1)))
    (i j : Fin k) : Finset (ι → Fin (k + 1)) :=
  if j < i then dhjInsensitivePreimage B j
  else if j = i then Finset.univ \ dhjInsensitivePreimage B j
  else Finset.univ

noncomputable def dhjFamilyMeet {k : ℕ} {ι : Type*} [Fintype ι]
    (D : Fin k → Finset (ι → Fin (k + 1))) : Finset (ι → Fin (k + 1)) := by
  classical
  exact Finset.univ.filter fun x => ∀ i, x ∈ D i

end MathlibExt.Combinatorics.DensityHalesJewettWanted
