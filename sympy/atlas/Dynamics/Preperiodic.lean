/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean -/

import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Dynamics.PeriodicPts.Defs
import Lean.Elab.Tactic.Omega

namespace Function

variable {α : Type*} {f : α → α} {x y z : α} {m n : ℕ}

/-!
# Forward and grand orbits

The forward orbit and preperiodicity follow
[Ghioca--Shadgar, arXiv:2607.26044v1](https://arxiv.org/abs/2607.26044v1), line 201.
The grand orbit follows
[Pasten--Silverman, arXiv:2307.12097v2](https://arxiv.org/abs/2307.12097v2), lines 635--661.
Preperiodicity of type `(m, n)` follows
[Sadek--Wafik--Yesin, arXiv:2403.04397v1](https://arxiv.org/abs/2403.04397v1),
lines 193--194.
-/

/-- Forward orbit of `x` under the self-map `f`. -/
def forwardOrbit (f : α → α) (x : α) : Set α :=
  Set.range fun n : ℕ => f^[n] x

@[simp]
theorem mem_forwardOrbit : y ∈ forwardOrbit f x ↔ ∃ n : ℕ, f^[n] x = y := by
  simp [forwardOrbit]

theorem mem_forwardOrbit_self (f : α → α) (x : α) : x ∈ forwardOrbit f x :=
  ⟨0, by simp⟩

theorem forwardOrbit_eq_range (f : α → α) (x : α) :
    forwardOrbit f x = Set.range (fun n : ℕ => f^[n] x) := rfl

/-- A point is preperiodic when its forward orbit is finite. -/
def IsPreperiodicPt (f : α → α) (x : α) : Prop :=
  (forwardOrbit f x).Finite

theorem isPreperiodicPt_iff_exists_eq_iterate :
    IsPreperiodicPt f x ↔ ∃ m n : ℕ, m < n ∧ f^[m] x = f^[n] x := by
  constructor
  · intro hfin
    have hinj : ¬Injective (fun n : ℕ => f^[n] x) := by
      intro hinj
      exact (Set.infinite_range_of_injective hinj) hfin
    obtain ⟨a, b, heq, hab⟩ := not_injective_iff.mp hinj
    by_cases h : a < b
    · exact ⟨a, b, h, heq⟩
    · exact ⟨b, a, by omega, heq.symm⟩
  · rintro ⟨m, n, hlt, heq⟩
    have hp : 0 < n - m := by omega
    have hperiodic : IsPeriodicPt f (n - m) (f^[m] x) := by
      rw [IsPeriodicPt]
      change f^[n - m] (f^[m] x) = f^[m] x
      rw [← iterate_add_apply]
      simpa [Nat.sub_add_cancel (Nat.le_of_lt hlt)] using heq.symm
    have hsub : forwardOrbit f x ⊆ Set.range (fun k : Fin n => f^[k.val] x) := by
      intro y hy
      rw [mem_forwardOrbit] at hy
      obtain ⟨k, rfl⟩ := hy
      by_cases hk : k < m
      · exact ⟨⟨k, hk.trans hlt⟩, rfl⟩
      · have hmk : m ≤ k := Nat.le_of_not_gt hk
        let t := k - m
        let r := t % (n - m)
        have hr : r < n - m := Nat.mod_lt _ hp
        refine ⟨⟨m + r, by omega⟩, ?_⟩
        calc
          f^[m + r] x = f^[r] (f^[m] x) := by
            rw [← iterate_add_apply]
            congr 1
            omega
          _ = f^[t] (f^[m] x) := hperiodic.iterate_mod_apply t
          _ = f^[m + t] x := by
            rw [← iterate_add_apply]
            congr 1
            omega
          _ = f^[k] x := by
            congr 1
            simp [t, Nat.add_sub_of_le hmk]
    exact (Set.finite_range _).subset hsub

/-- A strictly preperiodic point is preperiodic but not periodic. -/
def IsStrictlyPreperiodicPt (f : α → α) (x : α) : Prop :=
  IsPreperiodicPt f x ∧ x ∉ periodicPts f

@[simp]
theorem isStrictlyPreperiodicPt_iff :
    IsStrictlyPreperiodicPt f x ↔ IsPreperiodicPt f x ∧ x ∉ periodicPts f :=
  Iff.rfl

/-- A point is preperiodic of type `(m, n)` when its `m`th iterate has
positive period `n`. -/
def IsPreperiodicPtOfType (f : α → α) (m n : ℕ) (x : α) : Prop :=
  0 < n ∧ f^[m + n] x = f^[m] x

theorem isPreperiodicPtOfType_iff_isPeriodicPt :
    IsPreperiodicPtOfType f m n x ↔ 0 < n ∧ IsPeriodicPt f n (f^[m] x) := by
  constructor
  · rintro ⟨hn, h⟩
    refine ⟨hn, ?_⟩
    rw [IsPeriodicPt]
    change f^[n] (f^[m] x) = f^[m] x
    simpa only [← iterate_add_apply, Nat.add_comm] using h
  · rintro ⟨hn, h⟩
    refine ⟨hn, ?_⟩
    rw [IsPeriodicPt] at h
    change f^[n] (f^[m] x) = f^[m] x at h
    simpa only [← iterate_add_apply, Nat.add_comm] using h

theorem IsPreperiodicPtOfType.isPreperiodicPt
    (h : IsPreperiodicPtOfType f m n x) : IsPreperiodicPt f x := by
  rw [isPreperiodicPt_iff_exists_eq_iterate]
  exact ⟨m, m + n, Nat.lt_add_of_pos_right h.1, h.2.symm⟩

/-- Two points lie in the same grand orbit when two of their forward iterates agree. -/
def GrandOrbitRel (f : α → α) (x y : α) : Prop :=
  ∃ m n : ℕ, f^[m] x = f^[n] y

theorem grandOrbitRel_refl (f : α → α) (x : α) : GrandOrbitRel f x x :=
  ⟨0, 0, rfl⟩

theorem GrandOrbitRel.symm (h : GrandOrbitRel f x y) : GrandOrbitRel f y x := by
  obtain ⟨m, n, heq⟩ := h
  exact ⟨n, m, heq.symm⟩

theorem GrandOrbitRel.trans (hxy : GrandOrbitRel f x y) (hyz : GrandOrbitRel f y z) :
    GrandOrbitRel f x z := by
  obtain ⟨m₁, n₁, hxy⟩ := hxy
  obtain ⟨m₂, n₂, hyz⟩ := hyz
  refine ⟨m₁ + m₂, n₁ + n₂, ?_⟩
  calc
    f^[m₁ + m₂] x = f^[m₂] (f^[m₁] x) := by
      rw [← iterate_add_apply]
      congr 1
      omega
    _ = f^[m₂] (f^[n₁] y) := congrArg _ hxy
    _ = f^[n₁] (f^[m₂] y) := by
      rw [← iterate_add_apply, ← iterate_add_apply]
      congr 1
      omega
    _ = f^[n₁] (f^[n₂] z) := congrArg _ hyz
    _ = f^[n₁ + n₂] z := (iterate_add_apply f n₁ n₂ z).symm

theorem grandOrbitRel_equivalence (f : α → α) : Equivalence (GrandOrbitRel f) where
  refl := grandOrbitRel_refl f
  symm := GrandOrbitRel.symm
  trans := GrandOrbitRel.trans

/-- The setoid whose classes are grand orbits of `f`. -/
def grandOrbitSetoid (f : α → α) : Setoid α where
  r := GrandOrbitRel f
  iseqv := grandOrbitRel_equivalence f

/-- Grand orbit of `x`, viewed as its equivalence class. -/
def grandOrbit (f : α → α) (x : α) : Set α :=
  {y | GrandOrbitRel f x y}

@[simp]
theorem mem_grandOrbit : y ∈ grandOrbit f x ↔ GrandOrbitRel f x y := Iff.rfl

theorem grandOrbitRel_iff_inter_nonempty :
    GrandOrbitRel f x y ↔ (forwardOrbit f x ∩ forwardOrbit f y).Nonempty := by
  constructor
  · rintro ⟨m, n, heq⟩
    exact ⟨f^[m] x, ⟨⟨m, rfl⟩, ⟨n, heq.symm⟩⟩⟩
  · rintro ⟨w, ⟨⟨m, hm⟩, ⟨n, hn⟩⟩⟩
    exact ⟨m, n, hm.trans hn.symm⟩

end Function
