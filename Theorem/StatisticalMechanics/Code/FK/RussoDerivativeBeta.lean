/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBeta.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Def.StatisticalMechanics.Code.FK.RussoDerivativeBeta
open scoped BigOperators


namespace StatMech

namespace FK

open Finset ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


omit [DecidableEq V] in


lemma edgeProductW_pos {pf : Sym2 V → ℝ} (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    (ω : ConfigSpace (Sym2 V)) : 0 < edgeProductW G pf ω := by
  unfold edgeProductW
  apply Finset.prod_pos
  intro e _
  split
  · exact hpf e
  · have := hpf1 e; linarith


lemma fkWeightW_pos {pf : Sym2 V → ℝ} (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 0 < q) (ω : ConfigSpace (Sym2 V)) : 0 < fkWeightW G pf q ω :=
  mul_pos (edgeProductW_pos G hpf hpf1 ω) (pow_pos hq _)


lemma fkZW_pos {pf : Sym2 V → ℝ} (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 0 < q) : 0 < fkZW G pf q :=
  Finset.sum_pos (fun ω _ => fkWeightW_pos G hpf hpf1 hq ω) Finset.univ_nonempty

lemma fkZW_ne_zero {pf : Sym2 V → ℝ} (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 0 < q) : fkZW G pf q ≠ 0 :=
  (fkZW_pos G hpf hpf1 hq).ne'


end FK
end StatMech
