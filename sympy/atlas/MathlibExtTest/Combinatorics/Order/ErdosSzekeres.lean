/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Order/ErdosSzekeres.lean -/


import sympy.atlas.Combinatorics.Order.ErdosSzekeres
import Lemma.Finset.Order.ErdosSzekeres
import Mathlib.Tactic

open MathlibExt.Combinatorics.Order.ErdosSzekeres

/-- The migrated theorem retains the exact former Wanted signature. -/
example {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (f : Fin ((r - 1) * (s - 1) + 1) → ℝ) (hinj : Function.Injective f) :
    (∃ φ : Fin r → Fin ((r - 1) * (s - 1) + 1),
      (∀ i j : Fin r, i < j → φ i < φ j) ∧
      (∀ i j : Fin r, i < j → f (φ i) < f (φ j))) ∨
    (∃ ψ : Fin s → Fin ((r - 1) * (s - 1) + 1),
      (∀ i j : Fin s, i < j → ψ i < ψ j) ∧
      (∀ i j : Fin s, i < j → f (ψ j) < f (ψ i))) :=
  erdos_szekeres hr hs f hinj

/-- Boundary case `r = 1`: the full disjunction applies to length-one sequences. -/
example (s : ℕ) (hs : 0 < s)
    (f : Fin ((1 - 1) * (s - 1) + 1) → ℝ) (hinj : Function.Injective f) :
    (∃ φ : Fin 1 → Fin ((1 - 1) * (s - 1) + 1),
      (∀ i j : Fin 1, i < j → φ i < φ j) ∧
      (∀ i j : Fin 1, i < j → f (φ i) < f (φ j))) ∨
    (∃ ψ : Fin s → Fin ((1 - 1) * (s - 1) + 1),
      (∀ i j : Fin s, i < j → ψ i < ψ j) ∧
      (∀ i j : Fin s, i < j → f (ψ j) < f (ψ i))) :=
  erdos_szekeres (by norm_num) hs f hinj

/-- Boundary case `s = 1`: the full disjunction applies to length-one sequences. -/
example (r : ℕ) (hr : 0 < r)
    (f : Fin ((r - 1) * (1 - 1) + 1) → ℝ) (hinj : Function.Injective f) :
    (∃ φ : Fin r → Fin ((r - 1) * (1 - 1) + 1),
      (∀ i j : Fin r, i < j → φ i < φ j) ∧
      (∀ i j : Fin r, i < j → f (φ i) < f (φ j))) ∨
    (∃ ψ : Fin 1 → Fin ((r - 1) * (1 - 1) + 1),
      (∀ i j : Fin 1, i < j → ψ i < ψ j) ∧
      (∀ i j : Fin 1, i < j → f (ψ j) < f (ψ i))) :=
  erdos_szekeres hr (by norm_num) f hinj

/-- Small case `r = s = 2`: pairs contain a monotone pair. -/
example (f : Fin ((2 - 1) * (2 - 1) + 1) → ℝ)
    (hinj : Function.Injective f) :
    (∃ φ : Fin 2 → Fin ((2 - 1) * (2 - 1) + 1),
      (∀ i j : Fin 2, i < j → φ i < φ j) ∧
      (∀ i j : Fin 2, i < j → f (φ i) < f (φ j))) ∨
    (∃ ψ : Fin 2 → Fin ((2 - 1) * (2 - 1) + 1),
      (∀ i j : Fin 2, i < j → ψ i < ψ j) ∧
      (∀ i j : Fin 2, i < j → f (ψ j) < f (ψ i))) :=
  erdos_szekeres (by norm_num) (by norm_num) f hinj

/-- At `r = 1` the length-one increasing alternative always holds outright. -/
example (s : ℕ) (f : Fin ((1 - 1) * (s - 1) + 1) → ℝ) :
    ∃ φ : Fin 1 → Fin ((1 - 1) * (s - 1) + 1),
      (∀ i j : Fin 1, i < j → φ i < φ j) ∧
      (∀ i j : Fin 1, i < j → f (φ i) < f (φ j)) := by
  refine ⟨fun _ => ⟨0, Nat.succ_pos _⟩, ?_, ?_⟩
  · intro i j hij
    have h1 := i.isLt
    have h2 := j.isLt
    have hiv : i.val < j.val := Fin.lt_def.mp hij
    omega
  · intro i j hij
    have h1 := i.isLt
    have h2 := j.isLt
    have hiv : i.val < j.val := Fin.lt_def.mp hij
    omega

/-- At `s = 1` the length-one decreasing alternative always holds outright. -/
example (r : ℕ) (f : Fin ((r - 1) * (1 - 1) + 1) → ℝ) :
    ∃ ψ : Fin 1 → Fin ((r - 1) * (1 - 1) + 1),
      (∀ i j : Fin 1, i < j → ψ i < ψ j) ∧
      (∀ i j : Fin 1, i < j → f (ψ j) < f (ψ i)) := by
  refine ⟨fun _ => ⟨0, Nat.succ_pos _⟩, ?_, ?_⟩
  · intro i j hij
    have h1 := i.isLt
    have h2 := j.isLt
    have hiv : i.val < j.val := Fin.lt_def.mp hij
    omega
  · intro i j hij
    have h1 := i.isLt
    have h2 := j.isLt
    have hiv : i.val < j.val := Fin.lt_def.mp hij
    omega
