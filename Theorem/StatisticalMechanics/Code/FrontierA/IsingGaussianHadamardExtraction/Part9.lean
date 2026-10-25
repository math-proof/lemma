/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardLogDerivative.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.DyadicInverseSquareSummability.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.HadamardQuadraticFactorOrder
import Theorem.StatisticalMechanics.Code.FrontierA.EntireOrderMatchedQuotient
import Theorem.StatisticalMechanics.Code.FrontierA.EntireZeroFreeLogarithm
import Theorem.StatisticalMechanics.Code.FrontierA.EntireExponentialLogAffine
import Theorem.StatisticalMechanics.Code.FrontierA.EntireExponentialCharacteristicAffine
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Lindelof
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardExtraction.Part9
open Filter Metric
open scoped BigOperators ComplexConjugate


namespace StatMech.FrontierA

noncomputable section

theorem encodedCountableSequence_encode
    {α : Type*} [Countable α] (f : α → Real) (a : α) :
    encodedCountableSequence α f
      (@Encodable.encode α (Encodable.ofCountable α) a) = f a := by
  letI : Encodable α := Encodable.ofCountable α
  simp [encodedCountableSequence]

theorem encodedCountableSequence_eq_zero_of_notMem_range
    {α : Type*} [Countable α] (f : α → Real) (n : Nat)
    (hn : n ∉ Set.range
      (@Encodable.encode α (Encodable.ofCountable α))) :
    encodedCountableSequence α f n = 0 := by
  letI : Encodable α := Encodable.ofCountable α
  unfold encodedCountableSequence
  rw [show Encodable.decode₂ α n = none by
    exact Option.eq_none_iff_forall_not_mem.mpr fun a ha =>
      hn ⟨a, Encodable.mem_decode₂.mp ha⟩]

theorem exists_encode_eq_of_encodedCountableSequence_ne_zero
    {α : Type*} [Countable α] (f : α → Real) (n : Nat)
    (hn : encodedCountableSequence α f n ≠ 0) :
    ∃ a : α,
      @Encodable.encode α (Encodable.ofCountable α) a = n ∧
        encodedCountableSequence α f n = f a := by
  letI : Encodable α := Encodable.ofCountable α
  unfold encodedCountableSequence at hn ⊢
  split at *
  · rename_i a ha
    exact ⟨a, Encodable.decode₂_eq_some.mp ha, rfl⟩
  · exact (hn rfl).elim

theorem summable_encodedCountableSequence
    {α : Type*} [Countable α] {f : α → Real} (hf : Summable f) :
    Summable (encodedCountableSequence α f) := by
  letI : Encodable α := Encodable.ofCountable α
  let encode : α → Nat := Encodable.encode
  have hcomp : Summable (encodedCountableSequence α f ∘ encode) := by
    apply hf.congr
    intro a
    exact (encodedCountableSequence_encode f a).symm
  exact (Encodable.encode_injective.summable_iff
    (fun n hn => encodedCountableSequence_eq_zero_of_notMem_range f n hn)).mp hcomp

theorem tsum_encodedCountableSequence
    {α : Type*} [Countable α] (f : α → Real) :
    ∑' n, encodedCountableSequence α f n = ∑' a, f a := by
  letI : Encodable α := Encodable.ofCountable α
  let encode : α → Nat := Encodable.encode
  have hzero : ∀ n ∉ Set.range encode,
      encodedCountableSequence α f n = 0 := by
    intro n hn
    exact encodedCountableSequence_eq_zero_of_notMem_range f n hn
  have hsupport : Function.support (encodedCountableSequence α f) ⊆
      Set.range encode := by
    intro n hn
    by_contra hnrange
    exact hn (hzero n hnrange)
  calc
    ∑' n, encodedCountableSequence α f n =
        ∑' a, encodedCountableSequence α f (encode a) :=
      (Encodable.encode_injective.tsum_eq hsupport).symm
    _ = ∑' a, f a := by
      apply tsum_congr
      intro a
      exact encodedCountableSequence_encode f a

end
end StatMech.FrontierA
