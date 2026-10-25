/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.BallSphere
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.UniformSpace.HeineCantor


namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

/-! ## Tucker grid basic definitions and order lemmas -/

/-- Grid box: `z ∈ bu_tkBox n m` iff `|z i| ≤ m` for all `i`. -/
def bu_tkBox (n m : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun _ : Fin n => Finset.Icc (-(m : ℤ)) (m : ℤ)

/-- Freund–Todd step order: `w` is `z` with some coordinates pushed one unit away from `0`. -/
def bu_tkLe {n : ℕ} (z w : Fin n → ℤ) : Prop :=
  ∀ i, w i = z i ∨ (0 ≤ z i ∧ w i = z i + 1) ∨ (z i ≤ 0 ∧ w i = z i - 1)

/-- Chains: nonempty sets of pairwise comparable points (the simplices). -/
def bu_tkChain {n : ℕ} (σ : Finset (Fin n → ℤ)) : Prop :=
  σ.Nonempty ∧ ∀ z ∈ σ, ∀ w ∈ σ, bu_tkLe z w ∨ bu_tkLe w z

/-- Label negation: flips the sign, keeps the index. -/
def bu_tkNeg {n : ℕ} (l : Bool × Fin n) : Bool × Fin n := (!l.1, l.2)

/-- Sign set of a grid point: `(true, i)` for `z i > 0`, `(false, i)` for `z i < 0`. -/
def bu_tkSgn {n : ℕ} (z : Fin n → ℤ) : Finset (Bool × Fin n) :=
  (Finset.univ.filter fun i => z i ≠ 0).image fun i => (decide (0 < z i), i)

/-- Sign set of a chain (the sign set of its top vertex). -/
def bu_tkS {n : ℕ} (σ : Finset (Fin n → ℤ)) : Finset (Bool × Fin n) :=
  σ.sup bu_tkSgn

/-- Boundary: every point of `σ` has some coordinate of absolute value `m`. -/
def bu_tkBdry {n : ℕ} (m : ℕ) (σ : Finset (Fin n → ℤ)) : Prop :=
  ∀ z ∈ σ, ∃ i, |z i| = (m : ℤ)

/-- Happy chain: inside the box, a chain, and every sign is witnessed by a label. -/
def bu_tkHappy {n : ℕ} (m : ℕ) (L : (Fin n → ℤ) → Bool × Fin n)
    (σ : Finset (Fin n → ℤ)) : Prop :=
  σ ⊆ bu_tkBox n m ∧ bu_tkChain σ ∧ bu_tkS σ ⊆ σ.image L

/-- No complementary edge: no comparable pair in the box carries opposite labels. -/
def bu_tkNoCompl {n : ℕ} (m : ℕ) (L : (Fin n → ℤ) → Bool × Fin n) : Prop :=
  ∀ z ∈ bu_tkBox n m, ∀ w ∈ bu_tkBox n m, bu_tkLe z w → L w ≠ bu_tkNeg (L z)

/-- Height: sum of absolute values. Strictly increases along `bu_tkLe`. -/
def bu_tkH {n : ℕ} (z : Fin n → ℤ) : ℕ := ∑ i, (z i).natAbs

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
