/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/Entropy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Logic.Equiv.Fin.Basic
open Finset Real


namespace ShannonEntropy

/-- Definition 10.1.1 (Shannon entropy). For a probability mass function $p$ on a
finite type $S$, $H(p) = -\sum_s p_s \log p_s = \sum_s \text{negMulLog}(p_s)$. -/
noncomputable def shannonEntropy {S : Type*} [Fintype S] (p : PMF S) : ℝ :=
  ∑ s : S, negMulLog (p s).toReal

/-- Definition 10.1.6 (Conditional entropy). For a joint distribution $p$ on
$S \times T$ with marginal $p_T$, $H(X \mid Y) = \sum_t p_T(t) \sum_s \text{negMulLog}(p(s, t) / p_T(t))$. -/
noncomputable def conditionalEntropy {S T : Type*} [Fintype S] [Fintype T]
    (p : PMF (S × T)) : ℝ :=
  let margY := PMF.map Prod.snd p
  ∑ t : T, (margY t).toReal *
    ∑ s : S, negMulLog ((p (s, t)).toReal / (margY t).toReal)

section Helpers

/-- The $i$-th coordinate marginal of a PMF on $\alpha^n$. -/
noncomputable def marginal {n : ℕ} {α : Type*} [Fintype α]
    (p : PMF (Fin n → α)) (i : Fin n) : PMF α :=
  PMF.map (fun f => f i) p

end Helpers
end ShannonEntropy
