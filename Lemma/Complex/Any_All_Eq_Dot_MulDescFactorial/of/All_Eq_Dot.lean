import Lemma.Finset.AddSumIio.eq.SumIic
import Lemma.Finset.Any_In_IcoSumIio_SumIic.of.Eq_Sum
import Lemma.Finset.Eq.of.In_IcoSumIio_SumIic.In_IcoSumIio_SumIic
import Lemma.Matrix.DetOf_Sum_In_Ico_SumIio_SumIic.ne.Zero.of.EqSum.All_Ne
import Lemma.Polynomial.Any_Eq_Prod_SubXC.of.EqNatDegree.Monic
import Lemma.Finset.RootMultiplicityProd_SubXC.eq.CardSetOfEq
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.LinearRecurrence
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Interval.Finset.Fin
import Theorem.Function
import Theorem.Data.Fin.Dot.Part2
open Polynomial Matrix Finset
set_option maxHeartbeats 999999


/--
Closed form of a homogeneous linear recurrence of order `n` over `ℂ`:
`h[k + n] = c @ h[k: k + n]`. A root of multiplicity `m` contributes the
falling factorials of exponents `0, …, m - 1`, so a repeated root `0` still
frees the initial values.
-/
@[path]
private lemma main
  {n : ℕ}
  {h : ℕ ⇀ ℂ}
  {c : Fin n ⇀ ℂ}
-- given
  (hrec : ∀ k : ℕ, h[k + n] = c @ h[k: k + n]) :
-- imply
  ∃ (e : Fin n ⇀ ℕ) (r : Fin n ⇀ ℂ) (A : Fin n ⇀ ℂ), ∀ t : ℕ,
    h[t] = A @ fun i => t.descFactorial e[i] * r[i] ^ (t - e[i]) := by
-- proof
  classical
  let E : LinearRecurrence ℂ := ⟨n, fun i => c[i]⟩
  let p : ℂ[X] := E.charPoly
  have hpdeg : p.natDegree = n := by
    simpa [p, E] using natDegree_eq_of_degree_eq_some E.charPoly_degree_eq_order
  have hpmonic : p.Monic := by
    simpa [p] using E.charPoly_monic
  obtain ⟨rlin, hfactor⟩ := Any_Eq_Prod_SubXC.of.EqNatDegree.Monic hpmonic hpdeg
  let firsts : Finset (Fin n) :=
    Finset.univ.filter fun i => ∀ j : Fin n, j.val < i.val → rlin j ≠ rlin i
  let rd := firsts.card
  let iso := firsts.orderIsoOfFin (rfl : firsts.card = rd)
  let idx (k : Fin rd) : Fin n := iso k
  let x (k : Fin rd) : ℂ := rlin (idx k)
  let d (k : Fin rd) : ℕ := (Finset.univ.filter fun i => rlin i = x k).card
  have hdist : ∀ a b : Fin rd, a ≠ b → x a ≠ x b := by
    intro a b hab hx
    have hidx : idx a ≠ idx b := by
      intro h
      apply hab
      apply iso.injective
      exact Subtype.ext h
    obtain hlt | hlt := lt_or_gt_of_ne hidx
    ·
      have hb := (iso b).2
      simp only [firsts, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      exact hb (idx a) (Fin.lt_def.mp hlt) hx
    ·
      have ha := (iso a).2
      simp only [firsts, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      exact ha (idx b) (Fin.lt_def.mp hlt) hx.symm
  have hsum : ∑ k : Fin rd, d k = n := by
    have hdisj (a b : Fin rd) (hab : a ≠ b) :
      Disjoint (Finset.univ.filter fun i => rlin i = x a)
          (Finset.univ.filter fun i => rlin i = x b) := by
      rw [Finset.disjoint_left]
      intro i hi hi'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
      exact hdist a b hab (hi.symm.trans hi')
    have hunion :
      (Finset.univ.biUnion fun k : Fin rd => Finset.univ.filter fun i => rlin i = x k) =
          Finset.univ := by
      ext i
      constructor
      ·
        intro
        exact Finset.mem_univ _
      ·
        intro
        rw [Finset.mem_biUnion]
        let js := Finset.univ.filter fun j : Fin n => rlin j = rlin i
        have hjs : js.Nonempty := ⟨i, by simp [js]⟩
        let j := js.min' hjs
        have hjmem : j ∈ js := Finset.min'_mem js hjs
        have hjval : rlin j = rlin i := by
          simp only [js, Finset.mem_filter] at hjmem
          exact hjmem.2
        have hjfirst : j ∈ firsts := by
          simp only [firsts, Finset.mem_filter, Finset.mem_univ, true_and]
          intro j' hlt heq
          have hj' : j' ∈ js := by
            simp only [js, Finset.mem_filter, Finset.mem_univ, true_and]
            rw [heq, hjval]
          have hle := Finset.min'_le js j' hj'
          have hlej : (j : ℕ) ≤ j' := Fin.le_def.mp hle
          omega
        let k : Fin rd := iso.symm ⟨j, hjfirst⟩
        have hidx : idx k = j := by
          have : iso k = ⟨j, hjfirst⟩ := by
            simp [k]
          simpa only [idx] using congrArg Subtype.val this
        refine ⟨k, Finset.mem_univ _, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, x, hidx, hjval]
    have hcard :=
      Finset.card_biUnion (s := (Finset.univ : Finset (Fin rd)))
        (t := fun k => Finset.univ.filter fun i => rlin i = x k)
        (fun a _ b _ hab => hdisj a b hab)
    rw [hunion] at hcard
    simpa [d, Finset.card_univ] using hcard.symm
  have hdet :=
    DetOf_Sum_In_Ico_SumIio_SumIic.ne.Zero.of.EqSum.All_Ne
      (x := Fun.mk x) (d := Fun.mk d)
      (fun i j hij => by simpa [Fun.getElem_eq] using hdist i j hij)
      (by simpa [Fun.getElem_eq] using hsum)
  have hblock (i : Fin n) :
    ∃ k : Fin rd, (i : ℕ) ∈ Finset.Ico (∑ j ∈ Finset.Iio k, d j) (∑ j ∈ Finset.Iic k, d j) := by
    have hsumd : ∑ k : Fin rd, (Fun.mk d)[k] = n := by
      simpa [Fun.getElem_eq] using hsum
    obtain ⟨k, hk⟩ := Any_In_IcoSumIio_SumIic.of.Eq_Sum hsumd i
    refine ⟨k, ?_⟩
    dsimp only [GetElem.getElem] at hk
    apply hk
  let block (i : Fin n) : Fin rd := Classical.choose (hblock i)
  let ex (i : Fin n) : ℕ :=
    i - ∑ j ∈ Finset.Iio (block i), d j
  have hspec (i : Fin n) := Classical.choose_spec (hblock i)
  have hexlt (i : Fin n) : ex i < d (block i) := by
    have hi := hspec i
    simp only [Finset.mem_Ico] at hi
    have hle : ∑ j ∈ Finset.Iio (block i), d j ≤ i := by
      simpa [block] using hi.1
    have hlt : i < ∑ j ∈ Finset.Iio (block i), d j + d (block i) := by
      have h := AddSumIio.eq.SumIic (Fun.mk d) (block i)
      dsimp only [GetElem.getElem] at h
      rw [h]
      simpa [block] using hi.2
    simp only [ex]
    exact (Nat.sub_lt_iff_lt_add' hle).mpr hlt
  let root (i : Fin n) : ℂ := x (block i)
  let basis (i : Fin n) (t : ℕ) : ℂ :=
    t.descFactorial (ex i) * root i ^ (t - ex i)
  let M : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun t i => basis i t
  have hM : M.det ≠ 0 := by
    have hEq : M =
        Matrix.of fun (t i : Fin n) =>
          ∑ k : Fin rd,
            if (i : ℕ) ∈ Finset.Ico (∑ j ∈ Finset.Iio k, d j) (∑ j ∈ Finset.Iic k, d j) then
              (t : ℕ).descFactorial (i - ∑ j ∈ Finset.Iio k, d j) *
                x k ^ ((t : ℕ) - (i - ∑ j ∈ Finset.Iio k, d j))
            else 0 := by
      ext t i
      simp only [M, Matrix.of_apply, basis, root]
      rw [Finset.sum_eq_single_of_mem (block i) (Finset.mem_univ _)]
      ·
        have hi := hspec i
        rw [ite_eq_left hi]
      ·
        intro k' _ hk'
        have hnot :
          (i : ℕ) ∉ Finset.Ico (∑ j ∈ Finset.Iio k', d j) (∑ j ∈ Finset.Iic k', d j) := by
          intro hkmem
          apply hk'
          refine Eq.of.In_IcoSumIio_SumIic.In_IcoSumIio_SumIic
            (d := Fun.mk d) (t := i) (k₁ := k') (k₂ := block i) ?_ ?_
          ·
            dsimp only [GetElem.getElem]
            apply hkmem
          ·
            dsimp only [GetElem.getElem]
            apply hspec i
        simp [hnot]
    simpa [hEq] using hdet
  let bvec : Fin n → ℂ := fun i => h[i]
  let cvec : Fin n → ℂ := Matrix.mulVec M⁻¹ bvec
  have hMc : Matrix.mulVec M cvec = bvec := by
    rw [show cvec = Matrix.mulVec M⁻¹ bvec from rfl, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM), Matrix.one_mulVec]
  have hrow (i : Fin n) :
    h[i] = ∑ s : Fin n, cvec s * basis s i := by
    have hsumv := congr_fun hMc i
    rw [Matrix.mulVec_apply_eq_sum] at hsumv
    calc
      _ = bvec i := by simp [bvec]
      _ = ∑ s : Fin n, M i s * cvec s := by rw [← hsumv]
      _ = ∑ s : Fin n, cvec s * basis s i := by
        refine Finset.sum_congr rfl fun s _ => ?_
        simp [M]
        ring
  have hbasis (s : Fin n) : E.IsSolution (basis s) := by
    intro m
    let ρ : ℂ := root s
    let e : ℕ := ex s
    have he : e < p.rootMultiplicity ρ := by
      rw [hfactor, RootMultiplicityProd_SubXC.eq.CardSetOfEq]
      simpa [d, ρ, root, e] using hexlt s
    have hp0 : p ≠ 0 := hpmonic.ne_zero
    have hshift : X ^ m * p ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hp0
    have hmult : e < (X ^ m * p).rootMultiplicity ρ := by
      rw [rootMultiplicity_mul hshift]
      omega
    have hzero : (Nat.iterate derivative e (X ^ m * p)).eval ρ = 0 := by
      simpa [IsRoot] using isRoot_iterate_derivative_of_lt_rootMultiplicity hmult
    have hpX : p = X ^ n - ∑ i : Fin n, C c[i] * X ^ (i : ℕ) := by
      simp only [p, LinearRecurrence.charPoly, E]
      simp_rw [← C_mul_X_pow_eq_monomial]
      simp
    have hq : X ^ m * p =
        X ^ (m + n) - ∑ i : Fin n, C c[i] * X ^ (m + i) := by
      rw [hpX, mul_sub, Finset.mul_sum]
      congr 1
      · rw [← pow_add]
      ·
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    have hderiv : Nat.iterate derivative e (X ^ m * p) =
        C (((m + n).descFactorial e : ℂ)) * X ^ ((m + n) - e) -
          ∑ i : Fin n, C c[i] *
            (C (((m + i).descFactorial e : ℂ)) * X ^ ((m + i) - e)) := by
      rw [hq, iterate_derivative_sub, iterate_derivative_sum]
      simp_rw [iterate_derivative_C_mul, iterate_derivative_X_pow_eq_C_mul]
    rw [hderiv, eval_sub] at hzero
    have hpush (f : Fin n → ℂ[X]) : eval ρ (∑ i, f i) = ∑ i, eval ρ (f i) :=
      map_sum (evalRingHom ρ) f Finset.univ
    rw [hpush] at hzero
    simp only [eval_mul, eval_C, eval_pow, eval_X] at hzero
    rw [sub_eq_zero] at hzero
    simpa [basis, ρ, root, e, E, mul_assoc] using hzero
  let u : ℕ → ℂ := fun t => ∑ s : Fin n, cvec s * basis s t
  have hcombo : E.IsSolution u := by
    intro m
    show u (m + n) = ∑ i : Fin n, E.coeffs i * u (m + i)
    calc
      _ = ∑ s : Fin n, cvec s * basis s (m + n) := by simp [u]
      _ = ∑ s : Fin n, cvec s * ∑ i : Fin n, E.coeffs i * basis s (m + i) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [hbasis s m]
      _ = ∑ s : Fin n, ∑ i : Fin n, cvec s * (E.coeffs i * basis s (m + i)) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
      _ = ∑ i : Fin n, ∑ s : Fin n, cvec s * E.coeffs i * basis s (m + i) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => ?_
        ring
      _ = ∑ i : Fin n, E.coeffs i * ∑ s : Fin n, cvec s * basis s (m + i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        ring
      _ = ∑ i : Fin n, E.coeffs i * u (m + i) := by simp [u]
  have hEsol : E.IsSolution (fun t => h[t]) := by
    intro k
    simpa [E, LinearRecurrence.IsSolution, Dot.fun_getSlice_eq] using hrec k
  have hagree : Set.EqOn (fun t => h[t]) u ↑(Finset.range n) := by
    intro t ht
    simp only [Finset.mem_coe, Finset.mem_range] at ht
    simpa [u] using hrow ⟨t, ht⟩
  have hu : (fun t => h[t]) = u :=
    (E.eq_iff_eqOn_range_order (fun t => h[t]) u hEsol hcombo).mpr hagree
  refine ⟨⟨ex⟩, ⟨root⟩, ⟨cvec⟩, ?_⟩
  intro t
  simpa [u, basis, Fun.getElem_eq, Dot.fun_fin_eq] using congr_fun hu t


-- created on 2026-10-25
