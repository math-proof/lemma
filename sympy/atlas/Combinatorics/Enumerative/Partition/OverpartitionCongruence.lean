/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Multiset.Basic
import Mathlib.SetTheory.Cardinal.Finite
import sympy.atlas.Combinatorics.Enumerative.Partition.Overpartition
import Lemma.Nat.Enumerative.Partition.Overpartition
import Lemma.Nat.QuadraticForms.ThreeSquares
import Lemma.Real.SpecialFunctions.JacobiTripleProduct
import sympy.atlas.NumberTheory.QuadraticForms.ThreeSquares
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.ConvergenceRadius
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import sympy.atlas.Analysis.SpecialFunctions.JacobiTripleProduct
section

namespace MetaMathlibExt

open PowerSeries
open scoped PowerSeries.WithPiTopology

/-- Overpartition count: alias for the Wanted left-hand side. -/
private def opcOver (m : ℕ) : Type :=
  { p : Multiset ℕ × Finset ℕ //
    (∀ a ∈ p.1, 0 < a) ∧ p.1.sum = m ∧ ∀ a ∈ p.2, a ∈ p.1 }

-- SupportedMod
private def opcSupportedMod (R : Type*) [CommRing R] (p : ℕ) (r : ZMod p)
    (F : R⟦X⟧) : Prop :=
  ∀ n : ℕ, PowerSeries.coeff n F ≠ 0 → ((n : ℕ) : ZMod p) = r

private def opcSubsetPowerset (t : Finset ℕ) :
    ↥(t.powerset) ≃ {s : Finset ℕ // s ⊆ t} where
  toFun s := ⟨s.val, Finset.mem_powerset.mp s.property⟩
  invFun s := ⟨s.val, Finset.mem_powerset.mpr s.property⟩
  left_inv s := by obtain ⟨s, h⟩ := s; rfl
  right_inv s := by obtain ⟨s, h⟩ := s; rfl

private def opcOverSigma (m : ℕ) :
    opcOver m ≃ (Σ _π : m.Partition, {s : Finset ℕ // s ⊆ _π.parts.toFinset}) where
  toFun p := ⟨⟨p.val.1, fun {a} ha => p.property.1 a ha, p.property.2.1⟩,
    ⟨p.val.2, fun a ha => Multiset.mem_toFinset.mpr (p.property.2.2 a ha)⟩⟩
  invFun q := ⟨⟨q.1.parts, q.2.val⟩, fun a ha => q.1.parts_pos ha, q.1.parts_sum,
    fun a ha => Multiset.mem_toFinset.mp (q.2.property ha)⟩
  left_inv p := by obtain ⟨⟨M, S⟩, hpos, hsum, hsub⟩ := p; rfl
  right_inv q := by obtain ⟨⟨M, hpos, hsum⟩, ⟨S, hsub⟩⟩ := q; rfl

/-- Generating series of a weight function: the `k`-th coefficient counts the fiber. -/
private noncomputable def opcWeight {α : Type*} (w : α → ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun k => ((Nat.card {a // w a = k} : ℕ) : ℤ)

private def opcProdEquiv {α β : Type*} (w₁ : α → ℕ) (w₂ : β → ℕ) (N : ℕ) :
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

private def opcSumEquiv {α β : Type*} (w₁ : α → ℕ) (w₂ : β → ℕ) (N : ℕ) :
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
private noncomputable def opcThetaOn (P : ℤ → Prop) : ℤ⟦X⟧ :=
  opcWeight (fun x : {x : ℤ // P x} => x.val.natAbs ^ 2)

/-- The theta series `θ = Σ_{x ∈ ℤ} X^{x²}`. -/
private noncomputable def opcTheta : ℤ⟦X⟧ := opcThetaOn (fun _ => True)

/-- Reassociation equiv for the triple product. -/
private def opcReassoc :
    (({_x : ℤ // True} × {_x : ℤ // True}) × {_x : ℤ // True}) ≃ (ℤ × ℤ × ℤ) where
  toFun p := (p.1.1.val, p.1.2.val, p.2.val)
  invFun t := ((⟨t.1, trivial⟩, ⟨t.2.1, trivial⟩), ⟨t.2.2, trivial⟩)
  left_inv p := by obtain ⟨⟨⟨a, _⟩, ⟨b, _⟩⟩, ⟨c, _⟩⟩ := p; rfl
  right_inv t := by obtain ⟨a, b, c⟩ := t; rfl

private noncomputable def opcA : ℤ⟦X⟧ := opcThetaOn (fun x => x % 5 = 0)
private noncomputable def opcB : ℤ⟦X⟧ :=
  opcThetaOn (fun x => x % 5 = 1 ∨ x % 5 = 4)
private noncomputable def opcC : ℤ⟦X⟧ :=
  opcThetaOn (fun x => x % 5 = 2 ∨ x % 5 = 3)

private theorem opc_intCast_residue (x r : ℤ) (h : x % 5 = r) :
    ((x : ℤ) : ZMod 5) = ((r : ℤ) : ZMod 5) := by
  have h5 : (5 : ZMod 5) = 0 := by decide
  have hxx : x = 5 * (x / 5) + r := by omega
  rw [hxx]
  push_cast
  rw [h5, zero_mul, zero_add]

private theorem opc_supportA : opcSupportedMod ℤ 5 0 opcA := by
  apply opc_support_thetaOn
  intro x h0
  have h0' : x % 5 = 0 := h0
  have hx0 : ((x : ℤ) : ZMod 5) = 0 := by
    have h := opc_intCast_residue x 0 h0'
    rwa [Int.cast_zero] at h
  have hsq : (((x ^ 2 : ℤ)) : ZMod 5) = (((x : ℤ)) : ZMod 5) ^ 2 := by
    push_cast
    ring
  rw [hsq, hx0]
  simp

private theorem opc_supportB : opcSupportedMod ℤ 5 1 opcB := by
  apply opc_support_thetaOn
  intro x hx
  have hx' : x % 5 = 1 ∨ x % 5 = 4 := hx
  have hsq : (((x ^ 2 : ℤ)) : ZMod 5) = (((x : ℤ)) : ZMod 5) ^ 2 := by
    push_cast
    ring
  rcases hx' with h1 | h4
  · have hx1 : ((x : ℤ) : ZMod 5) = 1 := by
      have h := opc_intCast_residue x 1 h1
      rwa [Int.cast_one] at h
    rw [hsq, hx1, one_pow]
  · have hx4 : ((x : ℤ) : ZMod 5) = ((4 : ℤ) : ZMod 5) :=
      opc_intCast_residue x 4 h4
    rw [hsq, hx4]
    decide

private theorem opc_supportC : opcSupportedMod ℤ 5 4 opcC := by
  apply opc_support_thetaOn
  intro x hx
  have hx' : x % 5 = 2 ∨ x % 5 = 3 := hx
  have hsq : (((x ^ 2 : ℤ)) : ZMod 5) = (((x : ℤ)) : ZMod 5) ^ 2 := by
    push_cast
    ring
  rcases hx' with h2 | h3
  · have hx2 : ((x : ℤ) : ZMod 5) = ((2 : ℤ) : ZMod 5) :=
      opc_intCast_residue x 2 h2
    rw [hsq, hx2]
    decide
  · have hx3 : ((x : ℤ) : ZMod 5) = ((3 : ℤ) : ZMod 5) :=
      opc_intCast_residue x 3 h3
    rw [hsq, hx3]
    decide

private def opcSplitFwd
    (p : ((({x : ℤ // x % 5 = 0} ⊕ {x : ℤ // x % 5 = 1 ∨ x % 5 = 4})
    ⊕ {x : ℤ // x % 5 = 2 ∨ x % 5 = 3}))) : {_x : ℤ // True} :=
  match p with
  | .inl (.inl ⟨x, _⟩) => ⟨x, trivial⟩
  | .inl (.inr ⟨x, _⟩) => ⟨x, trivial⟩
  | .inr ⟨x, _⟩ => ⟨x, trivial⟩

private def opcSplitBwd (t : {_x : ℤ // True}) :
    ((({x : ℤ // x % 5 = 0} ⊕ {x : ℤ // x % 5 = 1 ∨ x % 5 = 4})
    ⊕ {x : ℤ // x % 5 = 2 ∨ x % 5 = 3})) :=
  if h0 : t.val % 5 = 0 then .inl (.inl ⟨t.val, h0⟩)
  else if h1 : t.val % 5 = 1 ∨ t.val % 5 = 4 then .inl (.inr ⟨t.val, h1⟩)
  else .inr ⟨t.val, by omega⟩

private theorem opcSplit_fwd_bwd (t : {_x : ℤ // True}) :
    opcSplitFwd (opcSplitBwd t) = t := by
  obtain ⟨x, _⟩ := t
  by_cases h0 : x % 5 = 0
  · simp [h0, opcSplitBwd, opcSplitFwd]
  · by_cases h1 : x % 5 = 1 ∨ x % 5 = 4
    · simp [h0, h1, opcSplitBwd, opcSplitFwd]
    · simp [h0, h1, opcSplitBwd, opcSplitFwd]

private theorem opcSplit_bwd_fwd
    (p : ((({x : ℤ // x % 5 = 0} ⊕ {x : ℤ // x % 5 = 1 ∨ x % 5 = 4})
    ⊕ {x : ℤ // x % 5 = 2 ∨ x % 5 = 3}))) :
    opcSplitBwd (opcSplitFwd p) = p := by
  match p with
  | .inl (.inl ⟨x, h0⟩) => simp [h0, opcSplitBwd, opcSplitFwd]
  | .inl (.inr ⟨x, h1⟩) =>
    have hn0 : ¬ x % 5 = 0 := by omega
    simp [hn0, h1, opcSplitBwd, opcSplitFwd]
  | .inr ⟨x, h2⟩ =>
    have hn0 : ¬ x % 5 = 0 := by omega
    have hn1 : ¬ (x % 5 = 1 ∨ x % 5 = 4) := by omega
    simp [hn0, hn1, opcSplitBwd, opcSplitFwd]

private def opcSplit :
    ((({x : ℤ // x % 5 = 0} ⊕ {x : ℤ // x % 5 = 1 ∨ x % 5 = 4})
    ⊕ {x : ℤ // x % 5 = 2 ∨ x % 5 = 3})) ≃ {_x : ℤ // True} where
  toFun := opcSplitFwd
  invFun := opcSplitBwd
  left_inv := opcSplit_bwd_fwd
  right_inv := opcSplit_fwd_bwd

private def opcSq (P Q : ℤ → Prop) (N : ℕ) : Type :=
  {t : ℤ × ℤ // P t.1 ∧ Q t.2 ∧ t.1 ^ 2 + t.2 ^ 2 = (((N : ℕ)) : ℤ)}

private def opcFiberSqEquiv (P Q : ℤ → Prop) (N : ℕ) :
    {p : {x : ℤ // P x} × {x : ℤ // Q x} //
      p.1.val.natAbs ^ 2 + p.2.val.natAbs ^ 2 = N} ≃ opcSq P Q N where
  toFun p := by
    obtain ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, h⟩ := p
    exact ⟨(x, y), hx, hy, by
      have h' : ((((x.natAbs ^ 2 + y.natAbs ^ 2 : ℕ))) : ℤ)
          = (((N : ℕ)) : ℤ) := by rw [h]
      simp only [Nat.cast_add, Nat.cast_pow, Int.natAbs_sq] at h'
      exact h'⟩
  invFun t := by
    obtain ⟨⟨x, y⟩, hx, hy, h⟩ := t
    exact ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, by
      have h' : ((((x.natAbs ^ 2 + y.natAbs ^ 2 : ℕ))) : ℤ)
          = (((N : ℕ)) : ℤ) := by
        simp only [Nat.cast_add, Nat.cast_pow, Int.natAbs_sq]
        exact h
      exact_mod_cast h'⟩
  left_inv p := by obtain ⟨⟨⟨x, _⟩, ⟨y, _⟩⟩, _⟩ := p; rfl
  right_inv t := by obtain ⟨⟨x, y⟩, _, _, _⟩ := t; rfl

private theorem opc_sq_zero (x : ℤ) (h : x % 5 = 0) :
    ((((x ^ 2 : ℤ))) : ZMod 5) = 0 := by
  have hx0 : ((x : ℤ) : ZMod 5) = 0 := by
    have hh := opc_intCast_residue x 0 h
    rwa [Int.cast_zero] at hh
  have hsq : ((((x ^ 2 : ℤ))) : ZMod 5) = (((x : ℤ)) : ZMod 5) ^ 2 := by
    push_cast
    ring
  rw [hsq, hx0]
  simp

private theorem opc_sq_one (x : ℤ) (h : x % 5 = 1 ∨ x % 5 = 4) :
    ((((x ^ 2 : ℤ))) : ZMod 5) = 1 := by
  have hsq : ((((x ^ 2 : ℤ))) : ZMod 5) = (((x : ℤ)) : ZMod 5) ^ 2 := by
    push_cast
    ring
  rcases h with h1 | h4
  · have hx1 : ((x : ℤ) : ZMod 5) = 1 := by
      have hh := opc_intCast_residue x 1 h1
      rwa [Int.cast_one] at hh
    rw [hsq, hx1, one_pow]
  · have hx4 : ((x : ℤ) : ZMod 5) = ((4 : ℤ) : ZMod 5) :=
      opc_intCast_residue x 4 h4
    rw [hsq, hx4]
    decide

private theorem opc_sq_four (x : ℤ) (h : x % 5 = 2 ∨ x % 5 = 3) :
    ((((x ^ 2 : ℤ))) : ZMod 5) = 4 := by
  have hsq : ((((x ^ 2 : ℤ))) : ZMod 5) = (((x : ℤ)) : ZMod 5) ^ 2 := by
    push_cast
    ring
  rcases h with h2 | h3
  · have hx2 : ((x : ℤ) : ZMod 5) = ((2 : ℤ) : ZMod 5) :=
      opc_intCast_residue x 2 h2
    rw [hsq, hx2]
    decide
  · have hx3 : ((x : ℤ) : ZMod 5) = ((3 : ℤ) : ZMod 5) :=
      opc_intCast_residue x 3 h3
    rw [hsq, hx3]
    decide

private theorem opc_dvd_add (x y : ℤ)
    (hmod : ((x : ZMod 5)) = 3 * ((y : ZMod 5))) : (5 : ℤ) ∣ x + 2 * y := by
  have h5 : (5 : ZMod 5) = 0 := by decide
  have e : ((((x + 2 * y : ℤ))) : ZMod 5) = 0 := by
    have e1 : ((((x + 2 * y : ℤ))) : ZMod 5)
        = ((x : ZMod 5)) + 2 * ((y : ZMod 5)) := by push_cast; ring
    have e2 : (3 : ZMod 5) * ((y : ZMod 5)) + 2 * ((y : ZMod 5))
        = 5 * ((y : ZMod 5)) := by ring
    rw [e1, hmod, e2, h5, zero_mul]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e

private theorem opc_dvd_sub (x y : ℤ)
    (hmod : ((x : ZMod 5)) = 3 * ((y : ZMod 5))) : (5 : ℤ) ∣ 2 * x - y := by
  have h5 : (5 : ZMod 5) = 0 := by decide
  have e : ((((2 * x - y : ℤ))) : ZMod 5) = 0 := by
    have e1 : ((((2 * x - y : ℤ))) : ZMod 5)
        = 2 * ((x : ZMod 5)) - ((y : ZMod 5)) := by push_cast; ring
    have e2 : 2 * ((3 : ZMod 5) * ((y : ZMod 5))) - ((y : ZMod 5))
        = 5 * ((y : ZMod 5)) := by ring
    rw [e1, hmod, e2, h5, zero_mul]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e

private def opcT (M : ℕ) : Type :=
  {t : ℤ × ℤ // t.1 ^ 2 + t.2 ^ 2 = ((((5 * M : ℕ))) : ℤ) ∧
    ((t.1 : ℤ) : ZMod 5) = 3 * ((t.2 : ℤ) : ZMod 5)}

private def opcPhi (M : ℕ) :
    opcSq (fun _ => True) (fun _ => True) M ≃ opcT M where
  toFun s := by
    obtain ⟨⟨u, v⟩, _, _, h⟩ := s
    exact ⟨(u + 2 * v, 2 * u - v), by
      have e : (u + 2 * v) ^ 2 + (2 * u - v) ^ 2 = 5 * (u ^ 2 + v ^ 2) := by
        ring
      have eM : ((((5 * M : ℕ))) : ℤ) = 5 * ((((M : ℕ))) : ℤ) := by
        push_cast
        ring
      rw [e, h, eM], by
        have e0 : ((((u + 2 * v) - 3 * (2 * u - v) : ℤ)) : ZMod 5) = 0 := by
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
          exact ⟨v - u, by push_cast; ring⟩
        have e1 : ((((u + 2 * v) - 3 * (2 * u - v) : ℤ)) : ZMod 5)
            = ((((u + 2 * v : ℤ))) : ZMod 5)
              - 3 * ((((2 * u - v : ℤ))) : ZMod 5) := by push_cast; ring
        rw [e1] at e0
        exact sub_eq_zero.mp e0⟩
  invFun t := by
    obtain ⟨⟨x, y⟩, heq, hmod⟩ := t
    have d1 : (5 : ℤ) ∣ x + 2 * y := opc_dvd_add x y hmod
    have d2 : (5 : ℤ) ∣ 2 * x - y := opc_dvd_sub x y hmod
    refine ⟨((x + 2 * y) / 5, (2 * x - y) / 5), trivial, trivial, ?_⟩
    have hu : 5 * ((x + 2 * y) / 5) = x + 2 * y := Int.mul_ediv_cancel' d1
    have hv : 5 * ((2 * x - y) / 5) = 2 * x - y := Int.mul_ediv_cancel' d2
    have key : 25 * ((((x + 2 * y) / 5) ^ 2 + ((2 * x - y) / 5) ^ 2 : ℤ))
        = 25 * ((((M : ℕ))) : ℤ) := by
      have e2 : 25 * ((((x + 2 * y) / 5) ^ 2 + ((2 * x - y) / 5) ^ 2 : ℤ))
          = (5 * ((x + 2 * y) / 5)) ^ 2 + (5 * ((2 * x - y) / 5)) ^ 2 := by
        ring
      have e3 : (5 * ((x + 2 * y) / 5)) ^ 2 + (5 * ((2 * x - y) / 5)) ^ 2
          = 5 * (x ^ 2 + y ^ 2) := by rw [hu, hv]; ring
      have eM : ((((5 * M : ℕ))) : ℤ) = 5 * ((((M : ℕ))) : ℤ) := by
        push_cast
        ring
      rw [e2, e3, heq, eM]
      ring
    have hfin : ((((x + 2 * y) / 5) ^ 2 + ((2 * x - y) / 5) ^ 2 : ℤ))
        = ((((M : ℕ))) : ℤ) :=
      mul_left_cancel₀ (show (25 : ℤ) ≠ 0 by norm_num) key
    exact hfin
  left_inv s := by
    obtain ⟨⟨u, v⟩, _, _, h⟩ := s
    apply Subtype.ext
    change ((u + 2 * v + 2 * (2 * u - v)) / 5, (2 * (u + 2 * v) - (2 * u - v)) / 5)
      = (u, v)
    have e1 : u + 2 * v + 2 * (2 * u - v) = 5 * u := by ring
    have e2 : 2 * (u + 2 * v) - (2 * u - v) = 5 * v := by ring
    rw [e1, e2]
    congr 1
    · have hd : (5 : ℤ) ∣ 5 * u := dvd_mul_right _ _
      have hh := Int.mul_ediv_cancel' hd
      exact mul_left_cancel₀ (show (5 : ℤ) ≠ 0 by norm_num) hh
    · have hd : (5 : ℤ) ∣ 5 * v := dvd_mul_right _ _
      have hh := Int.mul_ediv_cancel' hd
      exact mul_left_cancel₀ (show (5 : ℤ) ≠ 0 by norm_num) hh
  right_inv t := by
    obtain ⟨⟨x, y⟩, heq, hmod⟩ := t
    have d1 : (5 : ℤ) ∣ x + 2 * y := opc_dvd_add x y hmod
    have d2 : (5 : ℤ) ∣ 2 * x - y := opc_dvd_sub x y hmod
    have hu : 5 * ((x + 2 * y) / 5) = x + 2 * y := Int.mul_ediv_cancel' d1
    have hv : 5 * ((2 * x - y) / 5) = 2 * x - y := Int.mul_ediv_cancel' d2
    apply Subtype.ext
    change (((x + 2 * y) / 5 + 2 * ((2 * x - y) / 5)),
        (2 * ((x + 2 * y) / 5) - ((2 * x - y) / 5))) = (x, y)
    congr 1
    · have h5 : 5 * ((((x + 2 * y) / 5) + 2 * (((2 * x - y) / 5)) : ℤ))
          = 5 * x := by
        have e : 5 * ((((x + 2 * y) / 5) + 2 * (((2 * x - y) / 5)) : ℤ))
            = (5 * ((x + 2 * y) / 5)) + 2 * (5 * ((2 * x - y) / 5)) := by ring
        rw [e, hu, hv]
        ring
      exact mul_left_cancel₀ (show (5 : ℤ) ≠ 0 by norm_num) h5
    · have h5 : 5 * ((2 * (((x + 2 * y) / 5)) - (((2 * x - y) / 5)) : ℤ))
          = 5 * y := by
        have e : 5 * ((2 * (((x + 2 * y) / 5)) - (((2 * x - y) / 5)) : ℤ))
            = 2 * (5 * ((x + 2 * y) / 5)) - (5 * ((2 * x - y) / 5)) := by ring
        rw [e, hu, hv]
        ring
      exact mul_left_cancel₀ (show (5 : ℤ) ≠ 0 by norm_num) h5

-- Continued: the two-square dissection identity.

/-- In `ZMod 5`, squares equal to `1` come from `±1`. -/
private theorem opc_sq_eq_one_iff :
    ∀ a : ZMod 5, a ^ 2 = 1 ↔ a = 1 ∨ a = 4 := by
  decide

/-- In `ZMod 5`, squares equal to `4` come from `±2`. -/
private theorem opc_sq_eq_four_iff :
    ∀ a : ZMod 5, a ^ 2 = 4 ↔ a = 2 ∨ a = 3 := by
  decide

/-- Integer residues with square `1` mod 5 are `±1`. -/
private theorem opc_mem_pm1 (x : ℤ) (h : ((x : ZMod 5)) ^ 2 = 1) :
    x % 5 = 1 ∨ x % 5 = 4 := by
  have hx : ((x : ZMod 5)) = ((((x % 5 : ℤ))) : ZMod 5) :=
    opc_intCast_residue x _ rfl
  have h' : ((((x % 5 : ℤ))) : ZMod 5) ^ 2 = 1 := by rw [← hx]; exact h
  have hmem := (opc_sq_eq_one_iff _).mp h'
  rcases hmem with h1 | h4
  · have hd : (5 : ℤ) ∣ x % 5 - 1 := by
      have e : ((((x % 5 - 1 : ℤ))) : ZMod 5) = 0 := by
        have e1 : ((((x % 5 - 1 : ℤ))) : ZMod 5)
            = ((((x % 5 : ℤ))) : ZMod 5) - 1 := by push_cast; ring
        rw [e1, h1, sub_self]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e
    exact Or.inl (by omega)
  · have hd : (5 : ℤ) ∣ x % 5 - 4 := by
      have e : ((((x % 5 - 4 : ℤ))) : ZMod 5) = 0 := by
        have e1 : ((((x % 5 - 4 : ℤ))) : ZMod 5)
            = ((((x % 5 : ℤ))) : ZMod 5) - 4 := by push_cast; ring
        rw [e1, h4, sub_self]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e
    exact Or.inr (by omega)

/-- Integer residues with square `4` mod 5 are `±2`. -/
private theorem opc_mem_pm2 (y : ℤ) (h : ((y : ZMod 5)) ^ 2 = 4) :
    y % 5 = 2 ∨ y % 5 = 3 := by
  have hy : ((y : ZMod 5)) = ((((y % 5 : ℤ))) : ZMod 5) :=
    opc_intCast_residue y _ rfl
  have h' : ((((y % 5 : ℤ))) : ZMod 5) ^ 2 = 4 := by rw [← hy]; exact h
  have hmem := (opc_sq_eq_four_iff _).mp h'
  rcases hmem with h2 | h3
  · have hd : (5 : ℤ) ∣ y % 5 - 2 := by
      have e : ((((y % 5 - 2 : ℤ))) : ZMod 5) = 0 := by
        have e1 : ((((y % 5 - 2 : ℤ))) : ZMod 5)
            = ((((y % 5 : ℤ))) : ZMod 5) - 2 := by push_cast; ring
        rw [e1, h2, sub_self]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e
    exact Or.inl (by omega)
  · have hd : (5 : ℤ) ∣ y % 5 - 3 := by
      have e : ((((y % 5 - 3 : ℤ))) : ZMod 5) = 0 := by
        have e1 : ((((y % 5 - 3 : ℤ))) : ZMod 5)
            = ((((y % 5 : ℤ))) : ZMod 5) - 3 := by push_cast; ring
        rw [e1, h3, sub_self]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e
    exact Or.inr (by omega)

/-- A sum of two squares both divisible by 5 is zero mod 5. -/
private theorem opc_sq_add_zero_of_zero (x y : ℤ) (hx : x % 5 = 0)
    (hy : y % 5 = 0) : ((((x ^ 2 + y ^ 2 : ℤ))) : ZMod 5) = 0 := by
  have hpush : ((((x ^ 2 + y ^ 2 : ℤ))) : ZMod 5)
      = ((((x ^ 2 : ℤ))) : ZMod 5) + ((((y ^ 2 : ℤ))) : ZMod 5) := by
    push_cast; ring
  rw [hpush, opc_sq_zero x hx, opc_sq_zero y hy, add_zero]

/-- A `1 + 4` sum of squares is zero mod 5. -/
private theorem opc_sq_add_zero_of_mem (x y : ℤ)
    (hx : x % 5 = 1 ∨ x % 5 = 4) (hy : y % 5 = 2 ∨ y % 5 = 3) :
    ((((x ^ 2 + y ^ 2 : ℤ))) : ZMod 5) = 0 := by
  have hpush : ((((x ^ 2 + y ^ 2 : ℤ))) : ZMod 5)
      = ((((x ^ 2 : ℤ))) : ZMod 5) + ((((y ^ 2 : ℤ))) : ZMod 5) := by
    push_cast; ring
  rw [hpush, opc_sq_one x hx, opc_sq_four y hy]
  decide

/-- The two residue-class conditions cannot hold simultaneously off multiples
of 5: `x ≡ 3y` and `y ≡ 3x` force `5 ∣ y`. -/
private theorem opc_no_collide (x y : ℤ)
    (hmod : ((x : ZMod 5)) = 3 * ((y : ZMod 5)))
    (hcon : ((y : ZMod 5)) = 3 * ((x : ZMod 5))) : (5 : ℤ) ∣ y := by
  have hy0 : ((y : ZMod 5)) = 0 := by
    have h5 : (5 : ZMod 5) = 0 := by decide
    linear_combination 4 * hmod + 3 * hcon
      + ((x : ZMod 5) + (y : ZMod 5) * 2) * h5
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hy0

/-- The part of `opcT M` with `5 ∣ y` is the support of `a²`. -/
private def opcPart1 (M : ℕ) :
    {t : opcT M // (5 : ℤ) ∣ t.val.2} ≃
      opcSq (fun x => x % 5 = 0) (fun x => x % 5 = 0) (5 * M) where
  toFun t := by
    obtain ⟨⟨⟨x, y⟩, heq, hmod⟩, hdiv⟩ := t
    have hdiv' : (5 : ℤ) ∣ y := hdiv
    have hy0 : ((y : ZMod 5)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdiv'
    have hx0 : ((x : ZMod 5)) = 0 := by rw [hmod, hy0, mul_zero]
    have hxdvd : (5 : ℤ) ∣ x :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hx0
    exact ⟨(x, y), (by omega : x % 5 = 0), (by omega : y % 5 = 0), heq⟩
  invFun s := by
    obtain ⟨⟨x, y⟩, hx, hy, heq⟩ := s
    have hxdvd : (5 : ℤ) ∣ x := by omega
    have hydvd : (5 : ℤ) ∣ y := by omega
    have hx0 : ((x : ZMod 5)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hxdvd
    have hy0 : ((y : ZMod 5)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hydvd
    exact ⟨⟨(x, y), heq, by rw [hx0, hy0, mul_zero]⟩, hydvd⟩
  left_inv t := by obtain ⟨⟨⟨x, y⟩, _, _⟩, _⟩ := t; rfl
  right_inv s := by obtain ⟨⟨x, y⟩, _, _, _⟩ := s; rfl

/-- The cast equation in `ZMod 5`. -/
private theorem opc_fwd_hXY (M : ℕ) (x y : ℤ)
    (heq : x ^ 2 + y ^ 2 = (((5 * M : ℕ)) : ℤ)) :
    ((x : ZMod 5)) ^ 2 + ((y : ZMod 5)) ^ 2 = 0 := by
  have hcast : ((((x ^ 2 + y ^ 2 : ℤ))) : ZMod 5)
      = ((((5 * M : ℕ))) : ZMod 5) := by rw [heq, Int.cast_natCast]
  have h0 : ((((5 * M : ℕ))) : ZMod 5) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_mul_right 5 M)
  rw [h0] at hcast
  have hpush : ((((x ^ 2 + y ^ 2 : ℤ))) : ZMod 5)
      = ((x : ZMod 5)) ^ 2 + ((y : ZMod 5)) ^ 2 := by push_cast; ring
  rw [hpush] at hcast
  exact hcast

/-- Negated form of the cast equation. -/
private theorem opc_fwd_hneg (x y : ℤ)
    (hXY : ((x : ZMod 5)) ^ 2 + ((y : ZMod 5)) ^ 2 = 0) :
    ((x : ZMod 5)) ^ 2 = -((y : ZMod 5)) ^ 2 := by
  linear_combination hXY

/-- From the equation and `y ≡ ±2`, get `x ≡ ±1`. -/
private theorem opc_fwd_mem_left (M : ℕ) (x y : ℤ)
    (heq : x ^ 2 + y ^ 2 = (((5 * M : ℕ)) : ℤ))
    (hcase : y % 5 = 2 ∨ y % 5 = 3) : x % 5 = 1 ∨ x % 5 = 4 := by
  have hneg := opc_fwd_hneg x y (opc_fwd_hXY M x y heq)
  have hy2 : ((y : ZMod 5)) ^ 2 = 4 := by
    have hsq := opc_sq_four y hcase
    have hpush : ((((y ^ 2 : ℤ))) : ZMod 5) = ((y : ZMod 5)) ^ 2 := by
      push_cast; ring
    rw [← hpush]
    exact hsq
  have hx2 : ((x : ZMod 5)) ^ 2 = 1 := by
    rw [hneg, hy2]
    decide
  exact opc_mem_pm1 x hx2

/-- Off multiples of 5 and outside `±2`, the residue is `±1`. -/
private theorem opc_fwd_mem_y (y : ℤ) (hny : ¬ (5 : ℤ) ∣ y)
    (_hcase : ¬ (y % 5 = 2 ∨ y % 5 = 3)) : y % 5 = 1 ∨ y % 5 = 4 := by
  omega

/-- From the equation and `y ≡ ±1`, get `x ≡ ±2`. -/
private theorem opc_fwd_mem_right (M : ℕ) (x y : ℤ)
    (heq : x ^ 2 + y ^ 2 = (((5 * M : ℕ)) : ℤ))
    (hym : y % 5 = 1 ∨ y % 5 = 4) : x % 5 = 2 ∨ x % 5 = 3 := by
  have hneg := opc_fwd_hneg x y (opc_fwd_hXY M x y heq)
  have hy2 : ((y : ZMod 5)) ^ 2 = 1 := by
    have hsq := opc_sq_one y hym
    have hpush : ((((y ^ 2 : ℤ))) : ZMod 5) = ((y : ZMod 5)) ^ 2 := by
      push_cast; ring
    rw [← hpush]
    exact hsq
  have hx2 : ((x : ZMod 5)) ^ 2 = 4 := by
    rw [hneg, hy2]
    decide
  exact opc_mem_pm2 x hx2

/-- The swapped equation. -/
private theorem opc_fwd_eq_swap (M : ℕ) (x y : ℤ)
    (heq : x ^ 2 + y ^ 2 = (((5 * M : ℕ)) : ℤ)) :
    y ^ 2 + x ^ 2 = (((5 * M : ℕ)) : ℤ) := by
  linear_combination heq

/-- Forward map for the off-diagonal part: identity when `y ≡ ±2`,
swap when `y ≡ ±1`. -/
private def opcPart2Fwd (M : ℕ) (x y : ℤ)
    (heq : x ^ 2 + y ^ 2 = (((5 * M : ℕ)) : ℤ))
    (_hmod : ((x : ZMod 5)) = 3 * ((y : ZMod 5))) (hny : ¬ (5 : ℤ) ∣ y) :
    opcSq (fun x => x % 5 = 1 ∨ x % 5 = 4)
      (fun x => x % 5 = 2 ∨ x % 5 = 3) (5 * M) := by
  refine dite (y % 5 = 2 ∨ y % 5 = 3) (fun hcase => ?_) (fun hcase => ?_)
  · exact ⟨(x, y), opc_fwd_mem_left M x y heq hcase, hcase, heq⟩
  · exact ⟨(y, x), opc_fwd_mem_y y hny hcase,
      opc_fwd_mem_right M x y heq (opc_fwd_mem_y y hny hcase),
      opc_fwd_eq_swap M x y heq⟩

/-- Off `±1`, the second coordinate is not divisible by 5. -/
private theorem opc_bwd_hn (b : ℤ) (hb : b % 5 = 2 ∨ b % 5 = 3) :
    ¬ (5 : ℤ) ∣ b := by
  omega

/-- Off `±2`, the first coordinate is not divisible by 5. -/
private theorem opc_bwd_hna (a : ℤ) (ha : a % 5 = 1 ∨ a % 5 = 4) :
    ¬ (5 : ℤ) ∣ a := by
  omega

/-- The swapped-back equation. -/
private theorem opc_bwd_eq_swap (M : ℕ) (a b : ℤ)
    (heq : a ^ 2 + b ^ 2 = (((5 * M : ℕ)) : ℤ)) :
    b ^ 2 + a ^ 2 = (((5 * M : ℕ)) : ℤ) := by
  linear_combination heq

/-- From residues and the negated equation, recover `b ≡ 3a`. -/
private theorem opc_bwd_hba (a b : ℤ)
    (ha : a % 5 = 1 ∨ a % 5 = 4) (hb : b % 5 = 2 ∨ b % 5 = 3)
    (h : ¬ ((a : ZMod 5)) = 3 * ((b : ZMod 5))) :
    ((b : ZMod 5)) = 3 * ((a : ZMod 5)) := by
  rcases ha with ha1 | ha4 <;> rcases hb with hb2 | hb3
  · exfalso
    apply h
    have ea := opc_intCast_residue a 1 ha1
    have eb := opc_intCast_residue b 2 hb2
    rw [ea, eb]
    decide
  · have ea := opc_intCast_residue a 1 ha1
    have eb := opc_intCast_residue b 3 hb3
    rw [eb, ea]
    decide
  · have ea := opc_intCast_residue a 4 ha4
    have eb := opc_intCast_residue b 2 hb2
    rw [eb, ea]
    decide
  · exfalso
    apply h
    have ea := opc_intCast_residue a 4 ha4
    have eb := opc_intCast_residue b 3 hb3
    rw [ea, eb]
    decide

/-- Backward map for the off-diagonal part: undo the swap exactly when the
equation reads `b ≡ 3a` instead of `a ≡ 3b`. -/
private def opcPart2Bwd (M : ℕ) (a b : ℤ)
    (ha : a % 5 = 1 ∨ a % 5 = 4) (hb : b % 5 = 2 ∨ b % 5 = 3)
    (heq : a ^ 2 + b ^ 2 = (((5 * M : ℕ)) : ℤ)) :
    {t : opcT M // ¬ (5 : ℤ) ∣ t.val.2} := by
  refine dite (((a : ZMod 5)) = 3 * ((b : ZMod 5))) (fun h => ?_) (fun h => ?_)
  · exact ⟨⟨(a, b), heq, h⟩, opc_bwd_hn b hb⟩
  · exact ⟨⟨(b, a), opc_bwd_eq_swap M a b heq, opc_bwd_hba a b ha hb h⟩,
      opc_bwd_hna a ha⟩

/-- Computation rule: the forward map takes the identity branch. -/
private theorem opcPart2Fwd_pos (M : ℕ) (x y : ℤ)
    (heq : x ^ 2 + y ^ 2 = (((5 * M : ℕ)) : ℤ))
    (hmod : ((x : ZMod 5)) = 3 * ((y : ZMod 5))) (hny : ¬ (5 : ℤ) ∣ y)
    (hcase : y % 5 = 2 ∨ y % 5 = 3) :
    opcPart2Fwd M x y heq hmod hny
      = ⟨(x, y), opc_fwd_mem_left M x y heq hcase, hcase, heq⟩ := by
  unfold opcPart2Fwd
  exact dite_eq_left hcase

/-- Computation rule: the forward map takes the swap branch. -/
private theorem opcPart2Fwd_neg (M : ℕ) (x y : ℤ)
    (heq : x ^ 2 + y ^ 2 = (((5 * M : ℕ)) : ℤ))
    (hmod : ((x : ZMod 5)) = 3 * ((y : ZMod 5))) (hny : ¬ (5 : ℤ) ∣ y)
    (hcase : ¬ (y % 5 = 2 ∨ y % 5 = 3)) :
    opcPart2Fwd M x y heq hmod hny
      = ⟨(y, x), opc_fwd_mem_y y hny hcase,
        opc_fwd_mem_right M x y heq (opc_fwd_mem_y y hny hcase),
        opc_fwd_eq_swap M x y heq⟩ := by
  unfold opcPart2Fwd
  exact dite_eq_right hcase

/-- Computation rule: the backward map keeps the coordinates. -/
private theorem opcPart2Bwd_pos (M : ℕ) (a b : ℤ)
    (ha : a % 5 = 1 ∨ a % 5 = 4) (hb : b % 5 = 2 ∨ b % 5 = 3)
    (heq : a ^ 2 + b ^ 2 = (((5 * M : ℕ)) : ℤ))
    (h : ((a : ZMod 5)) = 3 * ((b : ZMod 5))) :
    opcPart2Bwd M a b ha hb heq = ⟨⟨(a, b), heq, h⟩, opc_bwd_hn b hb⟩ := by
  unfold opcPart2Bwd
  exact dite_eq_left h

/-- Computation rule: the backward map swaps the coordinates back. -/
private theorem opcPart2Bwd_neg (M : ℕ) (a b : ℤ)
    (ha : a % 5 = 1 ∨ a % 5 = 4) (hb : b % 5 = 2 ∨ b % 5 = 3)
    (heq : a ^ 2 + b ^ 2 = (((5 * M : ℕ)) : ℤ))
    (h : ¬ ((a : ZMod 5)) = 3 * ((b : ZMod 5))) :
    opcPart2Bwd M a b ha hb heq
      = ⟨⟨(b, a), opc_bwd_eq_swap M a b heq, opc_bwd_hba a b ha hb h⟩,
        opc_bwd_hna a ha⟩ := by
  unfold opcPart2Bwd
  exact dite_eq_right h

/-- The off-diagonal part of `opcT M` is the support of `b * c`. -/
private def opcPart2 (M : ℕ) :
    {t : opcT M // ¬ (5 : ℤ) ∣ t.val.2} ≃
      opcSq (fun x => x % 5 = 1 ∨ x % 5 = 4)
        (fun x => x % 5 = 2 ∨ x % 5 = 3) (5 * M) where
  toFun t := opcPart2Fwd M t.val.val.1 t.val.val.2
    t.val.property.1 t.val.property.2 t.property
  invFun s := opcPart2Bwd M s.val.1 s.val.2
    s.property.1 s.property.2.1 s.property.2.2
  left_inv t := by
    obtain ⟨⟨⟨x, y⟩, heq, hmod⟩, hny⟩ := t
    dsimp only
    by_cases hcase : y % 5 = 2 ∨ y % 5 = 3
    · rw [opcPart2Fwd_pos M x y heq hmod hny hcase,
        opcPart2Bwd_pos M x y _ _ heq hmod]
    · have hneg : ¬ ((y : ZMod 5)) = 3 * ((x : ZMod 5)) := by
        intro hcon
        exact hny (opc_no_collide x y hmod hcon)
      rw [opcPart2Fwd_neg M x y heq hmod hny hcase,
        opcPart2Bwd_neg M y x _ _ _ hneg]
  right_inv s := by
    obtain ⟨⟨a, b⟩, ha, hb, heq⟩ := s
    dsimp only
    by_cases h : ((a : ZMod 5)) = 3 * ((b : ZMod 5))
    · rw [opcPart2Bwd_pos M a b ha hb heq h,
        opcPart2Fwd_pos M a b heq h _ hb]
    · have hneg : ¬ (a % 5 = 2 ∨ a % 5 = 3) := by omega
      rw [opcPart2Bwd_neg M a b ha hb heq h,
        opcPart2Fwd_neg M b a _ _ _ hneg]

/-- `a² + b * c` is the 5-expansion of `θ²`. -/
private theorem opc_dissection_sq_add_mul_eq_expand :
    opcA ^ 2 + opcB * opcC
      = PowerSeries.expand 5 (by decide : (5 : ℕ) ≠ 0) (opcTheta ^ 2) := by
  apply PowerSeries.ext
  intro N
  have hLHS : PowerSeries.coeff N (opcA ^ 2 + opcB * opcC)
      = ((Nat.card (opcSq (fun x => x % 5 = 0) (fun x => x % 5 = 0) N) : ℕ) : ℤ)
        + ((Nat.card (opcSq (fun x => x % 5 = 1 ∨ x % 5 = 4)
            (fun x => x % 5 = 2 ∨ x % 5 = 3) N) : ℕ) : ℤ) := by
    unfold opcA opcB opcC
    rw [map_add, pow_two, opc_coeff_mul_thetaOn, opc_coeff_mul_thetaOn]
  rw [hLHS]
  by_cases hd : (5 : ℕ) ∣ N
  · obtain ⟨M, rfl⟩ := hd
    rw [PowerSeries.coeff_expand_mul]
    have hRHS : PowerSeries.coeff M (opcTheta ^ 2)
        = ((Nat.card (opcSq (fun _ => True) (fun _ => True) M) : ℕ) : ℤ) := by
      unfold opcTheta
      rw [pow_two, opc_coeff_mul_thetaOn]
    rw [hRHS, Nat.card_congr (opcPhi M), opc_card_split M, Nat.cast_add]
  · rw [PowerSeries.coeff_expand_of_not_dvd _ _ _ hd,
      opc_card_sq_eq_zero _ _ _ (fun x y hx hy =>
        opc_sq_add_zero_of_zero x y hx hy) hd,
      opc_card_sq_eq_zero _ _ _ (fun x y hx hy =>
        opc_sq_add_zero_of_mem x y hx hy) hd]
    simp

/-- The 5-dissection of `θ⁴`. -/
private theorem opc_theta_pow_four_decomp :
    ∃ W R₁ R₂ R₃ R₄ : ℤ⟦X⟧,
      opcSupportedMod ℤ 5 1 R₁ ∧ opcSupportedMod ℤ 5 2 R₂ ∧
        opcSupportedMod ℤ 5 3 R₃ ∧ opcSupportedMod ℤ 5 4 R₄ ∧
        opcTheta ^ 4 = PowerSeries.expand 5 opc_five_ne_zero (opcTheta ^ 4)
          + 5 • W + (R₁ + R₂ + R₃ + R₄) := by
  have mAA : opcSupportedMod ℤ 5 0 (opcA * opcA) :=
    opc_supportedMod_mul 5 0 0 _ _ opc_supportA opc_supportA
  have mAAA : opcSupportedMod ℤ 5 0 (opcA * opcA * opcA) :=
    opc_supportedMod_mul 5 0 0 _ _ mAA opc_supportA
  have mAAAB : opcSupportedMod ℤ 5 1 (opcA * opcA * opcA * opcB) :=
    opc_supportedMod_mul 5 0 1 _ _ mAAA opc_supportB
  have mBB : opcSupportedMod ℤ 5 2 (opcB * opcB) :=
    opc_supportedMod_mul 5 1 1 _ _ opc_supportB opc_supportB
  have mABB : opcSupportedMod ℤ 5 2 (opcA * (opcB * opcB)) :=
    opc_supportedMod_mul 5 0 2 _ _ opc_supportA mBB
  have mABBC : opcSupportedMod ℤ 5 1 (opcA * (opcB * opcB) * opcC) :=
    opc_supportedMod_mul 5 2 4 _ _ mABB opc_supportC
  have mCC : opcSupportedMod ℤ 5 3 (opcC * opcC) :=
    opc_supportedMod_mul 5 4 4 _ _ opc_supportC opc_supportC
  have mCCC : opcSupportedMod ℤ 5 2 (opcC * opcC * opcC) :=
    opc_supportedMod_mul 5 3 4 _ _ mCC opc_supportC
  have mCCCC : opcSupportedMod ℤ 5 1 (opcC * opcC * opcC * opcC) :=
    opc_supportedMod_mul 5 2 4 _ _ mCCC opc_supportC
  have mBBB : opcSupportedMod ℤ 5 3 (opcB * opcB * opcB) :=
    opc_supportedMod_mul 5 2 1 _ _ mBB opc_supportB
  have mAABB : opcSupportedMod ℤ 5 2 (opcA * opcA * (opcB * opcB)) :=
    opc_supportedMod_mul 5 0 2 _ _ mAA mBB
  have mBBBC : opcSupportedMod ℤ 5 2 (opcB * opcB * opcB * opcC) :=
    opc_supportedMod_mul 5 3 4 _ _ mBBB opc_supportC
  have mACCC : opcSupportedMod ℤ 5 2 (opcA * (opcC * opcC * opcC)) :=
    opc_supportedMod_mul 5 0 2 _ _ opc_supportA mCCC
  have mACC : opcSupportedMod ℤ 5 3 (opcA * opcA * (opcC * opcC)) :=
    opc_supportedMod_mul 5 0 3 _ _ mAA mCC
  have mBCCC : opcSupportedMod ℤ 5 3 (opcB * (opcC * opcC * opcC)) :=
    opc_supportedMod_mul 5 1 2 _ _ opc_supportB mCCC
  have mABBB : opcSupportedMod ℤ 5 3 (opcA * (opcB * opcB * opcB)) :=
    opc_supportedMod_mul 5 0 3 _ _ opc_supportA mBBB
  have mAAAC : opcSupportedMod ℤ 5 4 (opcA * opcA * opcA * opcC) :=
    opc_supportedMod_mul 5 0 4 _ _ mAAA opc_supportC
  have mAB : opcSupportedMod ℤ 5 1 (opcA * opcB) :=
    opc_supportedMod_mul 5 0 1 _ _ opc_supportA opc_supportB
  have mABCC : opcSupportedMod ℤ 5 4 (opcA * opcB * (opcC * opcC)) :=
    opc_supportedMod_mul 5 1 3 _ _ mAB mCC
  have mBBBB : opcSupportedMod ℤ 5 4 (opcB * opcB * opcB * opcB) :=
    opc_supportedMod_mul 5 3 1 _ _ mBBB opc_supportB
  refine ⟨2 • (opcA * opcA * opcB * opcC) + opcB * opcB * (opcC * opcC),
    4 • (opcA * opcA * opcA * opcB) + 12 • (opcA * (opcB * opcB) * opcC)
      + opcC * opcC * opcC * opcC,
    6 • (opcA * opcA * (opcB * opcB)) + 4 • (opcB * opcB * opcB * opcC)
      + 4 • (opcA * (opcC * opcC * opcC)),
    6 • (opcA * opcA * (opcC * opcC)) + 4 • (opcB * (opcC * opcC * opcC))
      + 4 • (opcA * (opcB * opcB * opcB)),
    4 • (opcA * opcA * opcA * opcC) + 12 • (opcA * opcB * (opcC * opcC))
      + opcB * opcB * opcB * opcB,
    ?_, ?_, ?_, ?_, ?_⟩
  · refine opc_supportedMod_add 5 1 _ _ ?_ ?_
    · refine opc_supportedMod_add 5 1 _ _ ?_ ?_
      · exact opc_supportedMod_nsmul 5 1 _ 4 mAAAB
      · exact opc_supportedMod_nsmul 5 1 _ 12 mABBC
    · exact mCCCC
  · refine opc_supportedMod_add 5 2 _ _ ?_ ?_
    · refine opc_supportedMod_add 5 2 _ _ ?_ ?_
      · exact opc_supportedMod_nsmul 5 2 _ 6 mAABB
      · exact opc_supportedMod_nsmul 5 2 _ 4 mBBBC
    · exact opc_supportedMod_nsmul 5 2 _ 4 mACCC
  · refine opc_supportedMod_add 5 3 _ _ ?_ ?_
    · refine opc_supportedMod_add 5 3 _ _ ?_ ?_
      · exact opc_supportedMod_nsmul 5 3 _ 6 mACC
      · exact opc_supportedMod_nsmul 5 3 _ 4 mBCCC
    · exact opc_supportedMod_nsmul 5 3 _ 4 mABBB
  · refine opc_supportedMod_add 5 4 _ _ ?_ ?_
    · refine opc_supportedMod_add 5 4 _ _ ?_ ?_
      · exact opc_supportedMod_nsmul 5 4 _ 4 mAAAC
      · exact opc_supportedMod_nsmul 5 4 _ 12 mABCC
    · exact mBBBB
  · have hpow : ((opcTheta ^ 2) ^ 2 : ℤ⟦X⟧) = opcTheta ^ 4 := by ring
    have hsq : (opcA ^ 2 + opcB * opcC) ^ 2
        = PowerSeries.expand 5 opc_five_ne_zero (opcTheta ^ 4) := by
      rw [opc_dissection_sq_add_mul_eq_expand, ← map_pow, hpow]
    conv_lhs => rw [opc_theta_eq_dissection]
    rw [← hsq]
    ring

/-- Theta fibers over `ℤ` match the `True`-subtype fibers. -/
private def opcThetaFiber (m : ℕ) :
    {x : Subtype (fun _ : ℤ => True) // x.val.natAbs ^ 2 = m} ≃
      {x : ℤ // x.natAbs ^ 2 = m} where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, trivial⟩, x.property⟩
  left_inv x := by obtain ⟨⟨_, _⟩, _⟩ := x; rfl
  right_inv x := by obtain ⟨_, _⟩ := x; rfl

/-- The sigma of square fibers over `ℕ` is `ℤ`. -/
private def opcSigmaTheta : (Σ _m : ℕ, {x : ℤ // x.natAbs ^ 2 = _m}) ≃ ℤ where
  toFun p := p.2.val
  invFun x := ⟨x.natAbs ^ 2, x, rfl⟩
  left_inv p := by obtain ⟨m, x, rfl⟩ := p; rfl
  right_inv x := rfl

/-- The mod-5 theta series. -/
private noncomputable def opcPhi5 : (ZMod 5)⟦X⟧ :=
  PowerSeries.map (Int.castRingHom (ZMod 5)) opcTheta

/-- The mod-5 twisted overpartition series. -/
private noncomputable def opcQ5 : (ZMod 5)⟦X⟧ :=
  PowerSeries.map (Int.castRingHom (ZMod 5)) (PowerSeries.rescale (-1 : ℤ)
    (Nat.Partition.genFun (fun _ _ ↦ (2 : ℤ))))

end MetaMathlibExt

end

namespace MetaMathlibExt

/--
For every positive `n`, the number of overpartitions of `5n` is congruent modulo `5`
to `(-1)ⁿ` times the number of ordered representations of `n` as three integer squares.

Liuquan Wang, "Another Proof of a Conjecture by Hirschhorn and Sellers on Overpartitions,"
Journal of Integer Sequences 17 (2014), Article 14.9.8,
Theorem (label thm1), lines 110–114.
`https://cs.uwaterloo.ca/journals/JIS/VOL17/Wang2/wang15.tex`

Proves `Wanted` entry `overpartition_mul_five_mod_five`.
-/
theorem overpartition_mul_five_mod_five
    (n : ℕ) (hn : 1 ≤ n) :
    Int.ModEq 5
      (Nat.card {
        p : Multiset ℕ × Finset ℕ //
          (∀ a ∈ p.1, 0 < a) ∧
          p.1.sum = 5 * n ∧
          ∀ a ∈ p.2, a ∈ p.1
      })
      (((-1 : ℤ) ^ n) * Nat.card {
        x : ℤ × ℤ × ℤ //
          x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = n
      }) := by
  obtain ⟨W, R₁, R₂, R₃, R₄, hR1, hR2, hR3, hR4, hdecomp⟩ :=
    opc_theta_pow_four_decomp
  have hfact : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hmap8 : opcPhi5 * opcQ5 = 1 := by
    have h := congrArg (PowerSeries.map (Int.castRingHom (ZMod 5)))
      opc_theta_mul_rescale_genFun
    rwa [map_mul, map_one] at h
  have hFrob : PowerSeries.expand 5 opc_five_ne_zero opcQ5 = opcQ5 ^ 5 := by
    have h0 : ((PowerSeries.expand 5 opc_five_ne_zero opcQ5).map
        (frobenius (ZMod 5) 5)) = opcQ5 ^ 5 :=
      PowerSeries.map_frobenius_expand 5 opc_five_ne_zero
    rw [ZMod.frobenius_zmod 5, PowerSeries.map_id] at h0
    exact h0
  have hQ : opcPhi5 ^ 4 * PowerSeries.expand 5 opc_five_ne_zero opcQ5
      = opcQ5 := by
    have h4 : opcPhi5 ^ 4 * opcQ5 ^ 5 = opcQ5 * (opcPhi5 * opcQ5) ^ 4 := by
      ring
    rw [hFrob, h4, hmap8, one_pow, mul_one]
  have hmap12 : opcPhi5 ^ 4
        = PowerSeries.expand 5 opc_five_ne_zero (opcPhi5 ^ 4)
          + (((PowerSeries.map (Int.castRingHom (ZMod 5)) R₁
            + PowerSeries.map (Int.castRingHom (ZMod 5)) R₂)
            + PowerSeries.map (Int.castRingHom (ZMod 5)) R₃)
            + PowerSeries.map (Int.castRingHom (ZMod 5)) R₄) := by
    have h := congrArg (PowerSeries.map (Int.castRingHom (ZMod 5))) hdecomp
    simp only [map_add, PowerSeries.map_expand, map_nsmul] at h
    rw [map_pow] at h
    have h5W : (5 : ℕ) • PowerSeries.map (Int.castRingHom (ZMod 5)) W
        = 0 := by
      have h5c : ∀ c : ZMod 5, (5 : ℕ) • c = 0 := by
        intro c
        rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      apply PowerSeries.ext
      intro k
      rw [map_nsmul]
      exact h5c _
    rw [h5W, add_zero] at h
    exact h
  have hz : ∀ (S : PowerSeries (ZMod 5)) (k : ZMod 5),
      opcSupportedMod (ZMod 5) 5 k S → k ≠ 0 →
        PowerSeries.coeff (5 * n)
          (S * PowerSeries.expand 5 opc_five_ne_zero opcQ5) = 0 := by
    intro S k hS hk
    have hE : opcSupportedMod (ZMod 5) 5 0
        (PowerSeries.expand 5 opc_five_ne_zero opcQ5) :=
      opc_supportedMod_expand 5 opc_five_ne_zero opcQ5
    have hP := opc_supportedMod_mul 5 k 0 _ _ hS hE
    have hk0 : k + 0 ≠ 0 := by simpa using hk
    have hNe : NeZero 5 := ⟨opc_five_ne_zero⟩
    exact opc_supportedMod_coeff_eq_zero 5 (k + 0) _ hP hk0 n
  have hk1 : (1 : ZMod 5) ≠ 0 := by
    intro h
    have h1 : (((1 : ℕ)) : ZMod 5) = 0 := by
      rw [Nat.cast_one]
      exact h
    exact absurd ((ZMod.natCast_eq_zero_iff 1 5).mp h1) (by omega)
  have hk2 : (2 : ZMod 5) ≠ 0 := by
    intro h
    have h2 : (((2 : ℕ)) : ZMod 5) = 0 := by simpa using h
    exact absurd ((ZMod.natCast_eq_zero_iff 2 5).mp h2) (by omega)
  have hk3 : (3 : ZMod 5) ≠ 0 := by
    intro h
    have h3 : (((3 : ℕ)) : ZMod 5) = 0 := by simpa using h
    exact absurd ((ZMod.natCast_eq_zero_iff 3 5).mp h3) (by omega)
  have hk4 : (4 : ZMod 5) ≠ 0 := by
    intro h
    have h4 : (((4 : ℕ)) : ZMod 5) = 0 := by simpa using h
    exact absurd ((ZMod.natCast_eq_zero_iff 4 5).mp h4) (by omega)
  have hz1 := hz _ (1 : ZMod 5)
    (opc_supportedMod_map (Int.castRingHom (ZMod 5)) 5 1 _ hR1) hk1
  have hz2 := hz _ (2 : ZMod 5)
    (opc_supportedMod_map (Int.castRingHom (ZMod 5)) 5 2 _ hR2) hk2
  have hz3 := hz _ (3 : ZMod 5)
    (opc_supportedMod_map (Int.castRingHom (ZMod 5)) 5 3 _ hR3) hk3
  have hz4 := hz _ (4 : ZMod 5)
    (opc_supportedMod_map (Int.castRingHom (ZMod 5)) 5 4 _ hR4) hk4
  have h43 : opcPhi5 ^ 4 * opcQ5 = opcPhi5 ^ 3 := by
    have e : opcPhi5 ^ 4 * opcQ5 = opcPhi5 ^ 3 * (opcPhi5 * opcQ5) := by
      ring
    rw [e, hmap8, mul_one]
  have e3 : PowerSeries.expand 5 opc_five_ne_zero (opcPhi5 ^ 4)
        * PowerSeries.expand 5 opc_five_ne_zero opcQ5
        = PowerSeries.expand 5 opc_five_ne_zero (opcPhi5 ^ 3) := by
    rw [← map_mul, h43]
  have hQeq : opcQ5 = PowerSeries.expand 5 opc_five_ne_zero (opcPhi5 ^ 3)
      + (((PowerSeries.map (Int.castRingHom (ZMod 5)) R₁
        * PowerSeries.expand 5 opc_five_ne_zero opcQ5
        + PowerSeries.map (Int.castRingHom (ZMod 5)) R₂
        * PowerSeries.expand 5 opc_five_ne_zero opcQ5)
        + PowerSeries.map (Int.castRingHom (ZMod 5)) R₃
        * PowerSeries.expand 5 opc_five_ne_zero opcQ5)
        + PowerSeries.map (Int.castRingHom (ZMod 5)) R₄
        * PowerSeries.expand 5 opc_five_ne_zero opcQ5) := by
    conv_lhs => rw [← hQ, hmap12]
    linear_combination e3
  have hcoeff : PowerSeries.coeff (5 * n) opcQ5
      = PowerSeries.coeff n (opcPhi5 ^ 3) := by
    rw [hQeq, map_add, map_add, map_add, map_add, hz1, hz2, hz3, hz4,
      PowerSeries.coeff_expand_mul]
    simp
  have hsign : (-1 : ZMod 5) ^ (5 * n) = (-1) ^ n := by
    rw [pow_mul, show ((-1 : ZMod 5) ^ 5) = -1 from Odd.neg_one_pow ⟨2, rfl⟩]
  have hLHS : PowerSeries.coeff (5 * n) opcQ5
      = (-1 : ZMod 5) ^ n
        * (Int.castRingHom (ZMod 5)) (PowerSeries.coeff (5 * n)
          (Nat.Partition.genFun (fun _ _ ↦ (2 : ℤ)))) := by
    unfold opcQ5
    rw [PowerSeries.coeff_map, PowerSeries.coeff_rescale, map_mul, map_pow,
      map_neg, map_one, hsign]
  have hRHS : PowerSeries.coeff n (opcPhi5 ^ 3)
      = (Int.castRingHom (ZMod 5)) (PowerSeries.coeff n (opcTheta ^ 3)) := by
    unfold opcPhi5
    rw [← map_pow, PowerSeries.coeff_map]
  have hN1 := opc_overpartition_card_eq_coeff_genFun (5 * n)
  have hN3 := opc_coeff_theta_cube n
  rw [← hN1] at hLHS
  rw [hN3] at hRHS
  -- hLHS : coeff-Q = (-1)^n * π ↑(card (opcOver (5n)))
  -- hRHS : coeff-Φ³ = π ↑(card three-sq)
  have hcomb : (-1 : ZMod 5) ^ n
        * (Int.castRingHom (ZMod 5))
          ((Nat.card (opcOver (5 * n)) : ℕ) : ℤ)
      = (Int.castRingHom (ZMod 5))
        ((Nat.card {x : ℤ × ℤ × ℤ //
          x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = (n : ℤ)} : ℕ) : ℤ) := by
    rw [← hLHS, ← hRHS]
    exact hcoeff
  have h2n : (-1 : ZMod 5) ^ n * (-1) ^ n = 1 := by
    rw [← pow_add, show n + n = 2 * n from by ring, pow_mul,
      show ((-1 : ZMod 5) ^ 2) = 1 from Even.neg_one_pow ⟨1, rfl⟩, one_pow]
  have hmain : (Int.castRingHom (ZMod 5))
        ((Nat.card (opcOver (5 * n)) : ℕ) : ℤ)
      = (-1 : ZMod 5) ^ n * (Int.castRingHom (ZMod 5))
        ((Nat.card {x : ℤ × ℤ × ℤ //
          x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = (n : ℤ)} : ℕ) : ℤ) := by
    calc (Int.castRingHom (ZMod 5))
            ((Nat.card (opcOver (5 * n)) : ℕ) : ℤ)
        = ((-1 : ZMod 5) ^ n * (-1) ^ n)
          * (Int.castRingHom (ZMod 5))
            ((Nat.card (opcOver (5 * n)) : ℕ) : ℤ) := by
          rw [h2n, one_mul]
      _ = (-1 : ZMod 5) ^ n * (((-1 : ZMod 5) ^ n
          * (Int.castRingHom (ZMod 5))
            ((Nat.card (opcOver (5 * n)) : ℕ) : ℤ))) := by
          rw [mul_assoc]
      _ = _ := by rw [← hcomb]
  have hOverEq : opcOver (5 * n) = { p : Multiset ℕ × Finset ℕ //
      (∀ a ∈ p.1, 0 < a) ∧ p.1.sum = 5 * n ∧ ∀ a ∈ p.2, a ∈ p.1 } := rfl
  have hcard : ((Nat.card { p : Multiset ℕ × Finset ℕ //
      (∀ a ∈ p.1, 0 < a) ∧ p.1.sum = 5 * n ∧ ∀ a ∈ p.2, a ∈ p.1 } : ℕ) : ℤ)
      = ((Nat.card (opcOver (5 * n)) : ℕ) : ℤ) := by
    rw [← hOverEq]
  have eNeg : (-1 : ZMod 5) ^ n
      = (Int.castRingHom (ZMod 5)) (((-1 : ℤ) ^ n)) := by
    rw [map_pow, map_neg, map_one]
  have hfin : ((((Nat.card (opcOver (5 * n)) : ℕ)) : ZMod 5))
      = ((((-1 : ℤ) ^ n * ((Nat.card {x : ℤ × ℤ × ℤ //
          x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = (n : ℤ)} : ℕ) : ℤ) : ℤ))
        : ZMod 5) := by
    have h := hmain
    rw [eNeg, ← map_mul] at h
    exact h
  rw [hcard]
  exact (ZMod.intCast_eq_intCast_iff _ _ _).mp hfin

end MetaMathlibExt

namespace Nat
namespace Overpartition
end Overpartition
end Nat
namespace Nat
end Nat
namespace MetaMathlibExt
end MetaMathlibExt
