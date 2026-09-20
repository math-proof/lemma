import Mathlib.MeasureTheory.Measure.WithDensity
import sympy.stats.joint_rv
import sympy.stats.symbolic_multivariate_probability
import torch.stack
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.DataGet.eq.GetUnflattenData
import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import sympy.Basic
open MeasureTheory Tensor Vector
set_option maxHeartbeats 2000000


/-- X[j] = X.get j for row-stacked tensors (Fin length proof alignment). -/
private lemma tensor_getElem_fin
  {n : ℕ} {s : List ℕ}
-- given
  (X : Tensor β (n :: s))
  (j : Fin n) :
-- imply
  X[j] = X.get j := by
-- proof
  change X.get ⟨↑j, _⟩ = X.get j
  apply congrArg
  apply Fin.ext
  rfl

/-- Get and expectation commute for row-stacks (data-vector Expectation). -/
private lemma expect_get
  [MeasurableSpace α] {n : ℕ} {s : List ℕ}
  {ν : Measure α}
-- given
  (g : α → Tensor ENNReal (n :: s))
  (j : Fin n) :
-- imply
  (expectation ν g)[j] = expectation ν (fun a ↦ (g a)[j]) := by
-- proof
  simp_rw [tensor_getElem_fin]
  apply Eq.of.EqDataS
  apply Vector.Eq.of.All_EqGetS.fin
  intro k
  have h1 := congrArg (fun v : List.Vector ENNReal s.prod => v.get k)
    (DataGet.eq.GetUnflattenData.fin (expectation ν g) j)
  have h2 := GetUnflatten.eq.Get_AddMul.fin (expectation ν g).data j k
  refine (h1.trans h2).trans ?_
  have hdata : (expectation ν g).data =
      List.Vector.ofFn fun i => expectation ν fun a => (g a).data.get i :=
    rfl
  simp only [hdata]
  erw [List.Vector.get_ofFn]
  have hR :
      (expectation ν (fun a ↦ (g a).get j)).data.get k =
        expectation ν (fun a ↦ ((g a).get j).data.get k) := by
    have : (expectation ν (fun a ↦ (g a).get j)).data =
        List.Vector.ofFn fun i =>
          expectation ν fun a => ((g a).get j).data.get i :=
      rfl
    rw [this, List.Vector.get_ofFn]
  refine Eq.trans ?_ hR.symm
  congr 1
  funext a
  have h1a := congrArg (fun v : List.Vector ENNReal s.prod => v.get k)
    (DataGet.eq.GetUnflattenData.fin (g a) j)
  have h2a := GetUnflatten.eq.Get_AddMul.fin (g a).data j k
  refine Eq.trans ?_ (h1a.trans h2a).symm
  rfl


@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure γ]
  [Countable α] [MeasurableSingletonClass α]
  {π : Measure Ω} {n : ℕ} {s : List ℕ}
  {x : Ω → Fin n → α} {y : Ω → γ}
  {f : α → Tensor ENNReal s}
-- given
  (hP : PSpace π (x, y))
  («y.bvar» : γ) :
-- imply
  𝔼[x: π]([k < n] f (x k) | y = «y.bvar») =
    [k < n] (𝔼[x: π](f (x k) | y = «y.bvar»)) := by
-- proof
  simp only [Expectation.condRV]
  let ν := ReferenceMeasure.measure.withDensity fun a ↦
    π.condProb (x, y) (a, «y.bvar»)
  change
    expectation ν (fun xv ↦ [k < n] f (xv k)) =
      [k < n] (expectation ν (fun xv ↦ f (xv k)))
  apply Tensor.Eq.of.All_EqGetS.fin
  intro j
  have hL :=
    expect_get (ν := ν) (fun xv : Fin n → _ ↦ ([k < n] f (xv k))) j
  simp_rw [tensor_getElem_fin] at hL
  have hMid :
      expectation ν (fun xv ↦ ([k < n] f (xv k)).get j) =
        expectation ν (fun xv ↦ f (xv j)) := by
    congr 1
    funext xv
    apply EqGetStack.fin (fun k : Fin n ↦ f (xv k)) j
  have hR :=
    EqGetStack.fin
      (fun k : Fin n ↦ expectation ν (fun xv ↦ f (xv k))) j
  apply hL.trans
  apply hMid.trans
  apply hR.symm


-- created on 2023-04-02
-- updated on 2026-09-21
