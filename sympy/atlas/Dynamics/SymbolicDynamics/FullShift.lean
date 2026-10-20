/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/SymbolicDynamics/FullShift.lean -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Dynamics.SymbolicDynamics.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Homeomorph.Defs

namespace SymbolicDynamics.FullShift

/-!
# One-dimensional finite full shifts

This file provides a common API for the full two-sided shift on `N` symbols,
its unit shift and automorphism group, and the jointly periodic-point notions
used for one-dimensional cellular automata.
-/

/-- The configuration space of the two-sided full shift on `N` symbols. -/
abbrev FullShiftSpace (N : ℕ) := ℤ → Fin N

/-- The unit left-translation of the two-sided full shift. -/
def unitShift (N : ℕ) : FullShiftSpace N → FullShiftSpace N :=
  shift (A := Fin N) (1 : ℤ)

@[simp]
theorem unitShift_apply (N : ℕ) (x : FullShiftSpace N) (i : ℤ) :
    unitShift N x i = x (1 + i) :=
  rfl

/-- The unit left-translation of the two-sided full shift, bundled as a homeomorphism. -/
def shiftHomeomorph (N : ℕ) : FullShiftSpace N ≃ₜ FullShiftSpace N where
  toFun := unitShift N
  invFun := shift (A := Fin N) (-1 : ℤ)
  left_inv x := by
    change shift (-1) (shift 1 x) = x
    rw [← shift_add]
    simp
  right_inv x := by
    change shift 1 (shift (-1) x) = x
    rw [← shift_add]
    simp
  continuous_toFun := continuous_shift 1
  continuous_invFun := continuous_shift (-1)

@[simp]
theorem shiftHomeomorph_apply (N : ℕ) (x : FullShiftSpace N) :
    shiftHomeomorph N x = unitShift N x :=
  rfl

@[simp]
theorem shiftHomeomorph_symm_apply (N : ℕ) (x : FullShiftSpace N) (i : ℤ) :
    (shiftHomeomorph N).symm x i = x (-1 + i) :=
  rfl

/-- Automorphisms of the full shift: homeomorphisms commuting with the unit shift. -/
def automorphismGroup (N : ℕ) : Subgroup (FullShiftSpace N ≃ₜ FullShiftSpace N) :=
  Subgroup.centralizer {shiftHomeomorph N}

/-- A one-dimensional cellular automaton, via the Curtis--Hedlund--Lyndon
characterization: a continuous self-map commuting with the unit shift. -/
def IsOneDimensionalCA (N : ℕ) (f : FullShiftSpace N → FullShiftSpace N) : Prop :=
  Continuous f ∧ Function.Commute f (unitShift N)

theorem isOneDimensionalCA_iff (N : ℕ) (f : FullShiftSpace N → FullShiftSpace N) :
    IsOneDimensionalCA N f ↔ Continuous f ∧ Function.Commute f (unitShift N) :=
  Iff.rfl

/-- The jointly periodic points of `f`: points periodic for `f` and periodic for
the unit shift. No common temporal period is required. -/
def jointlyPeriodicPoints (N : ℕ) (f : FullShiftSpace N → FullShiftSpace N) :
    Set (FullShiftSpace N) :=
  Function.periodicPts f ∩ Function.periodicPts (unitShift N)

@[simp]
theorem mem_jointlyPeriodicPoints (N : ℕ) (f : FullShiftSpace N → FullShiftSpace N)
    (x : FullShiftSpace N) :
    x ∈ jointlyPeriodicPoints N f ↔
      x ∈ Function.periodicPts f ∧ x ∈ Function.periodicPts (unitShift N) :=
  Iff.rfl

/-- The joint periodic count `P`: the number of points of shift-period `k` that
are also periodic for `f`. -/
noncomputable def jointPeriodicCount (N : ℕ)
    (f : FullShiftSpace N → FullShiftSpace N) (k : ℕ) : ℕ :=
  Set.ncard {x | Function.IsPeriodicPt (unitShift N) k x ∧ x ∈ Function.periodicPts f}

/-- The joint periodic growth rate `ν(f, S_N)`: the limsup of
`P ^ (1 / k)` over positive periods. The `k + 1` indexing enumerates exactly
the positive-period source sequence. -/
noncomputable def jointPeriodicGrowthRate (N : ℕ)
    (f : FullShiftSpace N → FullShiftSpace N) : ℝ :=
  Filter.limsup
    (fun k : ℕ =>
      Real.rpow (jointPeriodicCount N f (k + 1) : ℝ) (((k + 1 : ℕ) : ℝ)⁻¹))
    Filter.atTop

end SymbolicDynamics.FullShift
