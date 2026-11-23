/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Multiset.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Def.Combinatorics.Enumerative.Partition.Overpartition
public import Theorem.Nat.Enumerative.Partition.Overpartition
public import Theorem.Nat.QuadraticForms.ThreeSquares
public import Theorem.Real.SpecialFunctions.JacobiTripleProduct
public import Def.NumberTheory.QuadraticForms.ThreeSquares
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.GenFun
public import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Analytic.ConvergenceRadius
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Def.Analysis.SpecialFunctions.JacobiTripleProduct

@[expose] public section

section

namespace MetaMathlibExt

open PowerSeries

open scoped PowerSeries.WithPiTopology

/-- Overpartition count: alias for the Wanted left-hand side. -/
def opcOver (m : ℕ) : Type :=
  { p : Multiset ℕ × Finset ℕ //
    (∀ a ∈ p.1, 0 < a) ∧ p.1.sum = m ∧ ∀ a ∈ p.2, a ∈ p.1 }

-- SupportedMod
def opcSupportedMod (R : Type*) [CommRing R] (p : ℕ) (r : ZMod p)
    (F : R⟦X⟧) : Prop :=
  ∀ n : ℕ, PowerSeries.coeff n F ≠ 0 → ((n : ℕ) : ZMod p) = r

def opcSubsetPowerset (t : Finset ℕ) :
    ↥(t.powerset) ≃ {s : Finset ℕ // s ⊆ t} where
  toFun s := ⟨s.val, Finset.mem_powerset.mp s.property⟩
  invFun s := ⟨s.val, Finset.mem_powerset.mpr s.property⟩
  left_inv s := by obtain ⟨s, h⟩ := s; rfl
  right_inv s := by obtain ⟨s, h⟩ := s; rfl

def opcOverSigma (m : ℕ) :
    opcOver m ≃ (Σ _π : m.Partition, {s : Finset ℕ // s ⊆ _π.parts.toFinset}) where
  toFun p := ⟨⟨p.val.1, fun {a} ha => p.property.1 a ha, p.property.2.1⟩,
    ⟨p.val.2, fun a ha => Multiset.mem_toFinset.mpr (p.property.2.2 a ha)⟩⟩
  invFun q := ⟨⟨q.1.parts, q.2.val⟩, fun a ha => q.1.parts_pos ha, q.1.parts_sum,
    fun a ha => Multiset.mem_toFinset.mp (q.2.property ha)⟩
  left_inv p := by obtain ⟨⟨M, S⟩, hpos, hsum, hsub⟩ := p; rfl
  right_inv q := by obtain ⟨⟨M, hpos, hsum⟩, ⟨S, hsub⟩⟩ := q; rfl

/-- Generating series of a weight function: the `k`-th coefficient counts the fiber. -/
noncomputable def opcWeight {α : Type*} (w : α → ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun k => ((Nat.card {a // w a = k} : ℕ) : ℤ)

def opcProdEquiv {α β : Type*} (w₁ : α → ℕ) (w₂ : β → ℕ) (N : ℕ) :
    {p : α × β // w₁ p.1 + w₂ p.2 = N} ≃
      Σ _ij : ↥(Finset.HasAntidiagonal.antidiagonal N),
        ({a : α // w₁ a = _ij.1.1} × {b : β // w₂ b = _ij.1.2}) where
  toFun p :=
    ⟨⟨(w₁ p.val.1, w₂ p.val.2),
      Finset.HasAntidiagonal.mem_antidiagonal.mpr p.property⟩,
      ⟨p.val.1, rfl⟩, ⟨p.val.2, rfl⟩⟩
  invFun q := ⟨(q.2.1.val, q.2.2.val), by
    have ha := q.2.1.property
    have hb := q.2.2.property
    have hm := Finset.HasAntidiagonal.mem_antidiagonal.mp q.1.property
    change w₁ q.2.1.val + w₂ q.2.2.val = N
    rw [ha, hb]
    exact hm⟩
  left_inv p := by obtain ⟨⟨a, b⟩, hp⟩ := p; rfl
  right_inv q := by
    obtain ⟨⟨⟨i, j⟩, hmem⟩, ⟨a, ha⟩, ⟨b, hb⟩⟩ := q
    have e1 : w₁ a = i := ha
    have e2 : w₂ b = j := hb
    subst e1
    subst e2
    rfl

def opcSumEquiv {α β : Type*} (w₁ : α → ℕ) (w₂ : β → ℕ) (N : ℕ) :
    {x : α ⊕ β // Sum.elim w₁ w₂ x = N} ≃
      ({a : α // w₁ a = N} ⊕ {b : β // w₂ b = N}) where
  toFun x := match x with
    | ⟨.inl a, h⟩ => .inl ⟨a, h⟩
    | ⟨.inr b, h⟩ => .inr ⟨b, h⟩
  invFun x := match x with
    | .inl ⟨a, h⟩ => ⟨.inl a, h⟩
    | .inr ⟨b, h⟩ => ⟨.inr b, h⟩
  left_inv x := by obtain ⟨x, h⟩ := x; cases x <;> rfl
  right_inv x := by cases x <;> rfl

/-- Theta series restricted to a predicate on `ℤ`. -/
noncomputable def opcThetaOn (P : ℤ → Prop) : ℤ⟦X⟧ :=
  opcWeight (fun x : {x : ℤ // P x} => x.val.natAbs ^ 2)

/-- The theta series `θ = Σ_{x ∈ ℤ} X^{x²}`. -/
noncomputable def opcTheta : ℤ⟦X⟧ := opcThetaOn (fun _ => True)

/-- Reassociation equiv for the triple product. -/
def opcReassoc :
    (({_x : ℤ // True} × {_x : ℤ // True}) × {_x : ℤ // True}) ≃ (ℤ × ℤ × ℤ) where
  toFun p := (p.1.1.val, p.1.2.val, p.2.val)
  invFun t := ((⟨t.1, trivial⟩, ⟨t.2.1, trivial⟩), ⟨t.2.2, trivial⟩)
  left_inv p := by obtain ⟨⟨⟨a, _⟩, ⟨b, _⟩⟩, ⟨c, _⟩⟩ := p; rfl
  right_inv t := by obtain ⟨a, b, c⟩ := t; rfl

noncomputable def opcA : ℤ⟦X⟧ := opcThetaOn (fun x => x % 5 = 0)

noncomputable def opcB : ℤ⟦X⟧ :=
  opcThetaOn (fun x => x % 5 = 1 ∨ x % 5 = 4)

noncomputable def opcC : ℤ⟦X⟧ :=
  opcThetaOn (fun x => x % 5 = 2 ∨ x % 5 = 3)

end MetaMathlibExt
end
