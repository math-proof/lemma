import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.WithDensity
import sympy.stats.joint_rv
import sympy.stats.symbolic_multivariate_probability
import sympy.matrices.expressions.matmul
import torch.Tensor.item
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.Eq.is.Item
import Lemma.Tensor.GetData.eq.GetDataGet.of.Lt
import Lemma.Tensor.GetDot.eq.Sum_MulGetS
import Lemma.Tensor.ItemMul.eq.MulItemS
import Lemma.Tensor.Mul
import Lemma.Vector.GetSum.eq.Sum_Get
open Tensor


/-- For a length-m tensor, get-then-item is the flat data component. -/
private lemma item_get_eq_data_get
  {m : ℕ} (X : Tensor ENNReal [m]) (i : Fin m) :
  X[i].item = X.data.get ⟨i.val, by simp⟩ := by
  unfold Tensor.item
  have h := GetData.eq.GetDataGet.of.Lt (n := m) (i := (i : ℕ)) (h_i := i.isLt) X
  simpa [GetElem.getElem] using h.symm


/-- Get-then-item of a Tensor expectation equals expectation of get-then-item. -/
private lemma expect_get_item
  [MeasurableSpace α] {m : ℕ}
  (ν : MeasureTheory.Measure α)
  (g : α → Tensor ENNReal [m])
  (i : Fin m) :
  (expectation ν g)[i].item = expectation ν fun a ↦ (g a)[i].item := by
  let i' : Fin [m].prod := ⟨i.val, by simp⟩
  calc
    _ = (expectation ν g).data.get i' := item_get_eq_data_get _ i
    _ = (expectation ν fun a => (g a).data).get i' := rfl
    _ = expectation ν fun a => (g a).data.get i' := by
        change (List.Vector.ofFn fun j =>
            expectation ν fun a => (g a).data.get j).get i' =
          expectation ν fun a => (g a).data.get i'
        rw [List.Vector.get_ofFn]
    _ = expectation ν fun a => (g a)[i].item := by
        congr 1
        funext a
        exact (item_get_eq_data_get (g a) i).symm


/-- .item distributes over finite sums of scalar tensors. -/
private lemma item_finsetSum
  {ι : Type*} [DecidableEq ι]
  (s : Finset ι) (t : ι → Tensor ENNReal []) :
  (∑ i ∈ s, t i).item = ∑ i ∈ s, (t i).item := by
  let φ : Tensor ENNReal [] →+ List.Vector ENNReal 1 :=
    { toFun := fun x => x.data
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hdata : (∑ i ∈ s, t i).data = ∑ i ∈ s, (t i).data := map_sum φ t s
  have hget :=
    Vector.GetSum.eq.Sum_Get.fin (α := ENNReal) (n := 1) s
      (fun i => (t i).data) ⟨0, Nat.zero_lt_one⟩
  change
      (∑ i ∈ s, t i).data.get ⟨0, Nat.zero_lt_one⟩ =
        ∑ i ∈ s, (t i).data.get ⟨0, Nat.zero_lt_one⟩
  exact (congrArg (fun v : List.Vector ENNReal 1 =>
    v.get ⟨0, Nat.zero_lt_one⟩) hdata).trans hget


/-- (A @ v)[i].item expands as the ENNReal linear form in 
. -/
private lemma matvec_get_item
  {m k : ℕ}
  (A : Tensor ENNReal [m, k])
  (v : Tensor ENNReal [k])
  (i : Fin m) :
  ((A @ v)[i]'(by grind [matmul_shape])).item =
    ∑ p : Fin k, (A[i][p]).item * (v[p]).item := by
  have hrow := GetDot.eq.Sum_MulGetS.mv.fin (α := ENNReal) A v i
  calc
    _ = (∑ p : Fin k,
            id (α := Tensor ENNReal []) A[i][p] *
              id (α := Tensor ENNReal []) v[p]).item :=
          congrArg Tensor.item hrow
    _ = ∑ p : Fin k,
          (id (α := Tensor ENNReal []) A[i][p] *
            id (α := Tensor ENNReal []) v[p]).item :=
          item_finsetSum _ _
    _ = ∑ p : Fin k, (A[i][p]).item * (v[p]).item := by
        refine Finset.sum_congr rfl ?_
        intro p _
        set Ai := id (α := Tensor ENNReal []) A[i][p]
        set vp := id (α := Tensor ENNReal []) v[p]
        change (Ai * vp).item = Ai.item * vp.item
        have hm : Ai * vp = Mul.mul Ai vp := Tensor.Mul Ai vp
        have hi := ItemMul.eq.MulItemS Ai vp
        calc
          _ = (Mul.mul Ai vp).item := by rw [hm]
          _ = Ai.item * vp.item := hi


/--
Pull a constant Tensor matrix–vector product (@ / Dot.dot / insum) through
(unconditional) expectation.

Python: Random.Expect_Dot.eq.Dot_Expect — Expectation(A @ x) = A @ Expectation(x)
when A is non-random.

| attributes | lemma |
| :---: | :---: |
| main | Random.Expect_Dot.eq.Dot_Expect |
| comm | Random.Dot_Expect.eq.Expect_Dot |
-/
@[main, comm]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  [Countable α] [MeasurableSingletonClass α]
  {π : MeasureTheory.Measure Ω} {m k : ℕ}
  {a : Ω → α}
  {f : α → Tensor ENNReal [k]}
-- given
  (hP : PSpace π a)
  (A : Tensor ENNReal [m, k])
  (hf : ∀ p : Fin k, Measurable (fun x : α ↦ (f x)[p].item)) :
-- imply
  𝔼[a: π](A @ f a) = A @ 𝔼[a: π](f a) := by
-- proof
  -- matmul_shape [m, k] [k] = [m] definitionally, so both sides are Tensor _ [m].
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.Item
  simp only [Expectation.ofRV]
  have hL := expect_get_item (π.map a) (fun x ↦ A @ f x) i
  refine Eq.trans hL ?_
  have hlin :
      expectation (π.map a) (fun x ↦ (A @ f x)[i].item) =
        ∑ p : Fin k, (A[i][p]).item *
          expectation (π.map a) (fun x ↦ (f x)[p].item) := by
    have h1 :
        expectation (π.map a) (fun x ↦ (A @ f x)[i].item) =
          expectation (π.map a)
            (fun x ↦ ∑ p : Fin k, (A[i][p]).item * (f x)[p].item) := by
      congr 1
      funext x
      -- unify getElem proof with matvec_get_item
      change ((A @ f x)[i]'(by grind [matmul_shape])).item =
        ∑ p : Fin k, (A[i][p]).item * (f x)[p].item
      exact matvec_get_item A (f x) i
    refine h1.trans ?_
    simp only [expectation_ennreal]
    rw [MeasureTheory.lintegral_finsetSum (μ := π.map a) (Finset.univ : Finset (Fin k))
      fun p _ => (hf p).const_mul ((A[i][p]).item)]
    refine Finset.sum_congr rfl ?_
    intro p _
    exact MeasureTheory.lintegral_const_mul ((A[i][p]).item) (hf p)
  refine hlin.trans ?_
  have hR :
      (A @ expectation (π.map a) f)[i].item =
        ∑ p : Fin k, (A[i][p]).item *
          (expectation (π.map a) f)[p].item := by
    change ((A @ expectation (π.map a) f)[i]'(by grind [matmul_shape])).item =
      ∑ p : Fin k, (A[i][p]).item * (expectation (π.map a) f)[p].item
    exact matvec_get_item A (expectation (π.map a) f) i
  refine Eq.trans ?_ hR.symm
  congr 1
  funext p
  congr 1
  exact (expect_get_item (π.map a) f p).symm


-- created on 2023-04-07
-- updated on 2026-09-26
