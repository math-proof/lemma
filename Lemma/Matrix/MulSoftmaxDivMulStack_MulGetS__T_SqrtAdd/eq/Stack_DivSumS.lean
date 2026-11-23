import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Module.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring
import Syntax.LinearAlgebra.Matrix.Notation
import Syntax.LinearAlgebra.Matrix.Pow
import Lemma.Matrix.EqRotaryOn__01.of.All_Any_In_Brace.All_Ne.Injective.Injective
import Lemma.Fin.RopeEven.ne.RopeOdd
import Lemma.Fin.Any_In_BraceRopeEven__RopeOdd
import Lemma.Fin.InjectiveRopeEven
import Lemma.Fin.InjectiveRopeOdd
import Lemma.Matrix.InvRotary'.eq.TRotary'
import Lemma.Matrix.InvRotaryOn.eq.TRotaryOn.of.All_EqSum__Add.All_OrAnyS_Eq.All_Ne.Injective.Injective
import Lemma.Matrix.MulSoftmaxDivMulStack_MulGetS__T_SqrtAdd.eq.StackAnd__DivSumSFin.of.Eq_1.All_Eq_Inv.All_EqDotS_Mul
import Lemma.Matrix.MulT_RotaryOn.eq.RotaryOn__Sub.of.All_EqSum__Add.All_OrAnyS_Eq.All_Ne.Injective.Injective
import Lemma.Fin.Sum.eq.AddSumS
open Fin Matrix Real
open scoped Matrix
set_option maxHeartbeats 800000


private lemma sum_if_and_comm
  {d : ℕ}
  {p q : Fin d → Prop} [DecidablePred p] [DecidablePred q]
-- given
  (f : Fin d → ℝ) :
-- imply
  (∑ t : Fin d, if p t ∧ q t then f t else 0) =
    ∑ t : Fin d, if q t ∧ p t then f t else 0 := by
-- proof
  refine Finset.sum_congr rfl fun t _ => ?_
  if h : p t ∧ q t then
    rw [ite_eq_left h, ite_eq_left h.symm]
  else
    have h' : ¬ (q t ∧ p t) := fun hc => h hc.symm
    rw [ite_eq_right h, ite_eq_right h']

private lemma natAdd_inj
-- given
  (d : ℕ) :
-- imply
  Function.Injective (Fin.natAdd d : Fin d → Fin (d + d)) := by
-- proof
  intro a b h
  ext
  have := congrArg Fin.val h
  simp [Fin.natAdd] at this
  omega

private lemma half_disj
-- given
  (d : ℕ)
  (t s : Fin d) :
-- imply
  Fin.castAdd d t ≠ Fin.natAdd d s := by
-- proof
  intro h
  have := congrArg Fin.val h
  simp [Fin.castAdd, Fin.natAdd] at this
  have := t.isLt
  omega

private lemma half_surj
-- given
  (d : ℕ)
  (i : Fin (d + d)) :
-- imply
  (∃ t : Fin d, Fin.castAdd d t = i) ∨ (∃ t : Fin d, Fin.natAdd d t = i) := by
-- proof
  if h : (i : ℕ) < d then
    refine Or.inl ⟨⟨(i : ℕ), h⟩, ?_⟩
    ext
    rfl
  else
    refine Or.inr ⟨⟨(i : ℕ) - d, ?_⟩, ?_⟩
    ·
      have := i.isLt
      omega
    ·
      ext
      simp [Fin.natAdd]
      omega

private lemma sum_half
  {d : ℕ}
-- given
  (f : Fin (d + d) → ℝ) :
-- imply
  ∑ i, f i = ∑ t : Fin d, f (Fin.castAdd d t) + ∑ t : Fin d, f (Fin.natAdd d t) := by
-- proof
  let e := finSumFinEquiv (m := d) (n := d)
  have hs : ∑ i, f i = ∑ s : Fin d ⊕ Fin d, f (e s) := (e.sum_comp f).symm
  rw [hs, Fintype.sum_sum_type]
  refine congrArg₂ HAdd.hAdd ?_ ?_
  ·
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [e, finSumFinEquiv_apply_left]
  ·
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [e, finSumFinEquiv_apply_right]

private lemma rotaryOn_neg
  {d : ℕ}
  {u v : Fin d → Fin (d + d)}
-- given
  (θ : Fin d → ℝ) :
-- imply
  Matrix.rotaryOn u v (-θ) = (Matrix.rotaryOn u v θ)ᵀ := by
-- proof
  ext i j
  have hL :
    Matrix.rotaryOn u v (-θ) i j =
      (∑ t : Fin d, if i = u t ∧ j = u t then Real.cos (θ t) else 0) +
      (∑ t : Fin d, if i = u t ∧ j = v t then Real.sin (θ t) else 0) +
      (∑ t : Fin d, if i = v t ∧ j = u t then -Real.sin (θ t) else 0) +
      (∑ t : Fin d, if i = v t ∧ j = v t then Real.cos (θ t) else 0) := by
    simp only [Matrix.rotaryOn, Matrix.of_apply, Pi.neg_apply, Finset.sum_add_distrib, Real.cos_neg,
      Real.sin_neg, neg_neg]
  have hR :
    (Matrix.rotaryOn u v θ)ᵀ i j =
      (∑ t : Fin d, if j = u t ∧ i = u t then Real.cos (θ t) else 0) +
      (∑ t : Fin d, if j = u t ∧ i = v t then -Real.sin (θ t) else 0) +
      (∑ t : Fin d, if j = v t ∧ i = u t then Real.sin (θ t) else 0) +
      (∑ t : Fin d, if j = v t ∧ i = v t then Real.cos (θ t) else 0) := by
    simp only [Matrix.transpose_apply, Matrix.rotaryOn, Matrix.of_apply, Finset.sum_add_distrib]
  rw [hL, hR]
  rw [sum_if_and_comm (p := fun t => i = u t) (q := fun t => j = u t) (f := fun t => Real.cos (θ t))]
  rw [sum_if_and_comm (p := fun t => i = u t) (q := fun t => j = v t) (f := fun t => Real.sin (θ t))]
  rw [sum_if_and_comm (p := fun t => i = v t) (q := fun t => j = u t) (f := fun t => -Real.sin (θ t))]
  rw [sum_if_and_comm (p := fun t => i = v t) (q := fun t => j = v t) (f := fun t => Real.cos (θ t))]
  ring

private lemma dot_of
  {d : ℕ}
  {u v : Fin d → Fin (d + d)}
-- given
  (hu : Function.Injective u)
  (hv : Function.Injective v)
  (huv : ∀ t s, u t ≠ v s)
  (hsurj : ∀ i : Fin (d + d), (∃ t, u t = i) ∨ (∃ t, v t = i))
  (hsum : ∀ f : Fin (d + d) → ℝ, ∑ i, f i = ∑ t, f (u t) + ∑ t, f (v t))
  (α β : Fin d → ℝ)
  (q k : Fin (d + d) → ℝ) :
-- imply
  Matrix.rotaryOn u v α *ᵥ q ⬝ᵥ Matrix.rotaryOn u v β *ᵥ k =
    q ⬝ᵥ Matrix.rotaryOn u v (β - α) *ᵥ k := by
-- proof
  have hmul := MulT_RotaryOn.eq.RotaryOn__Sub.of.All_EqSum__Add.All_OrAnyS_Eq.All_Ne.Injective.Injective hu hv huv hsurj hsum α β
  rw [← hmul, ← Matrix.mulVec_mulVec, dotProduct_comm]
  exact (Matrix.dotProduct_transpose_mulVec (Matrix.rotaryOn u v α) q
    (Matrix.rotaryOn u v β *ᵥ k)).symm

private lemma rotary_dot
  {d : ℕ}
-- given
  (α β : Fin d → ℝ)
  (q k : Fin (d + d) → ℝ) :
-- imply
  Matrix.rotary α *ᵥ q ⬝ᵥ Matrix.rotary β *ᵥ k =
    q ⬝ᵥ Matrix.rotary (β - α) *ᵥ k := by
-- proof
  simpa [Matrix.rotary] using
    dot_of (Fin.castAdd_injective d d) (natAdd_inj d) (half_disj d) (half_surj d)
      (sum_half (d := d)) α β q k

private lemma rotary_neg
  {d : ℕ}
-- given
  (φ : Fin d → ℝ) :
-- imply
  Matrix.rotary (-φ) = (Matrix.rotary φ)ᵀ := by
-- proof
  simpa [Matrix.rotary] using rotaryOn_neg (u := Fin.castAdd d) (v := Fin.natAdd d) φ

private lemma rotary_zero
  {d : ℕ} :
-- imply
  Matrix.rotary (0 : Fin d → ℝ) = 1 := by
-- proof
  simpa [Matrix.rotary] using
    EqRotaryOn__01.of.All_Any_In_Brace.All_Ne.Injective.Injective (Fin.castAdd_injective d d) (natAdd_inj d) (half_disj d)
      (fun i => by
        obtain h | h := half_surj d i
        ·
          obtain ⟨t, ht⟩ := h
          refine ⟨t, ?_⟩
          rw [Set.mem_insert_iff, Set.mem_singleton_iff]
          exact Or.inl ht.symm
        ·
          obtain ⟨t, ht⟩ := h
          refine ⟨t, ?_⟩
          rw [Set.mem_insert_iff, Set.mem_singleton_iff]
          exact Or.inr ht.symm)

private lemma rotary_inv
  {d : ℕ}
-- given
  (φ : Fin d → ℝ) :
-- imply
  (Matrix.rotary φ)⁻¹ = (Matrix.rotary φ)ᵀ := by
-- proof
  simpa [Matrix.rotary] using
    InvRotaryOn.eq.TRotaryOn.of.All_EqSum__Add.All_OrAnyS_Eq.All_Ne.Injective.Injective (Fin.castAdd_injective d d) (natAdd_inj d) (half_disj d) (half_surj d)
      (sum_half (d := d)) φ

private lemma rotary'_dot
  {d : ℕ}
-- given
  (α β : Fin d → ℝ)
  (q k : Fin (d + d) → ℝ) :
-- imply
  Matrix.rotary' α *ᵥ q ⬝ᵥ Matrix.rotary' β *ᵥ k =
    q ⬝ᵥ Matrix.rotary' (β - α) *ᵥ k := by
-- proof
  simpa [Matrix.rotary'] using
    dot_of (InjectiveRopeEven d) (InjectiveRopeOdd d) (RopeEven.ne.RopeOdd d)
      (fun i => by
        obtain ⟨t, ht⟩ := Any_In_BraceRopeEven__RopeOdd d i
        obtain h | h := by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ht
        · exact Or.inl ⟨t, h.symm⟩
        · exact Or.inr ⟨t, h.symm⟩)
      Sum.eq.AddSumS α β q k

private lemma rotary'_neg
  {d : ℕ}
-- given
  (φ : Fin d → ℝ) :
-- imply
  Matrix.rotary' (-φ) = (Matrix.rotary' φ)ᵀ := by
-- proof
  simpa [Matrix.rotary'] using rotaryOn_neg (u := stepEven) (v := stepOdd) φ

private lemma rotary'_zero
  {d : ℕ} :
-- imply
  Matrix.rotary' (0 : Fin d → ℝ) = 1 := by
-- proof
  simpa [Matrix.rotary'] using
    EqRotaryOn__01.of.All_Any_In_Brace.All_Ne.Injective.Injective (InjectiveRopeEven d) (InjectiveRopeOdd d) (RopeEven.ne.RopeOdd d)
      (Any_In_BraceRopeEven__RopeOdd d)

/--
Rotary attention collapses to relative angles when each frequency row is linear in the token index.

The usual schedule is `θ[i][j] = λ * i / b ^ (j / d)`. Here that is weakened to `θ[i][j] = τ j * i`.
`Matrix.rotary` is the half-split rotation, with planes `(j, j + d)`.
-/
@[path]
private lemma main
  {n d : ℕ}
  {τ : Fin d → ℝ}
-- given
  (Q K V : ℝ ^ [n, d + d]) :
-- imply
  let θ := [i < n] ((i : ℝ) • τ)
  let R (i : Fin n) := θ[i].rotary
  let Rₑ (i k : Fin n) :=
    R[(k - i : ℤ).natAbs] ^ (k - i : ℤ).sign
  (([i < n] (R[i] *ᵥ Q[i])) *
      ([i < n] (R[i] *ᵥ K[i]))ᵀ / √(d + d : ℝ)).softmax * V =
    [i < n][j < d + d]
      (∑ k : Fin n, V[k][j] * (Q[i] ⬝ᵥ Rₑ[i][k] *ᵥ K[k] / √(d + d : ℝ)).exp) /
        ∑ k : Fin n,
          (R[i] *ᵥ Q[i] ⬝ᵥ R[k] *ᵥ K[k] / √(d + d : ℝ)).exp := by
-- proof
  apply MulSoftmaxDivMulStack_MulGetS__T_SqrtAdd.eq.StackAnd__DivSumSFin.of.Eq_1.All_Eq_Inv.All_EqDotS_Mul
    rotary_dot (fun φ => (rotary_neg φ).trans (rotary_inv φ).symm) rotary_zero Q K V

/-- Adjacent-pair form of the same identity. `Matrix.rotary'` rotates planes `(2j, 2j + 1)`. -/
@[path]
private lemma interleave
  {n d : ℕ}
  {τ : Fin d → ℝ}
-- given
  (Q K V : ℝ ^ [n, d + d]) :
-- imply
  let θ := [i < n] ((i : ℝ) • τ)
  let R (i : Fin n) := θ[i].rotary'
  let Rₑ (i k : Fin n) :=
    R[(k - i : ℤ).natAbs] ^ (k - i : ℤ).sign
  (([i < n] (R[i] *ᵥ Q[i])) *
      ([i < n] (R[i] *ᵥ K[i]))ᵀ / √(d + d : ℝ)).softmax * V =
    [i < n][j < d + d]
      (∑ k : Fin n, V[k][j] * (Q[i] ⬝ᵥ Rₑ[i][k] *ᵥ K[k] / √(d + d : ℝ)).exp) /
        ∑ k : Fin n,
          (R[i] *ᵥ Q[i] ⬝ᵥ R[k] *ᵥ K[k] / √(d + d : ℝ)).exp := by
-- proof
  apply MulSoftmaxDivMulStack_MulGetS__T_SqrtAdd.eq.StackAnd__DivSumSFin.of.Eq_1.All_Eq_Inv.All_EqDotS_Mul
    rotary'_dot (fun φ => (rotary'_neg φ).trans (InvRotary'.eq.TRotary' φ).symm) rotary'_zero Q K V


-- created on 2023-06-09
-- updated on 2026-11-23
