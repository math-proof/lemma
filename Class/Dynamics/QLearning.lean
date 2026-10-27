import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Def.Dynamics.MarkovDecisionProcess.Part5
import Abbrev.Analysis.InnerProductSpace.EuclideanVec
import Def.Dynamics.QLearning
open Finset

universe u v

/-!
# Tabular Q-learning

Ported from rl-theory-in-lean `RLTheory/Algorithm/QLearning.lean`.

Q-tables are Euclidean vectors indexed by `Fin (Fintype.card (S × A))`, through the fixed
enumeration `QLearningSpec.sa_to_fin` / `QLearningSpec.fin_to_sa` (rl: `sa_to_fin` / `fin_to_sa`).

* The sup norm (rl: `‖·‖∞` on `LinftySpace d := PiLp ⊤ _`) is Mathlib's `Pi` norm of the plain
  coordinates, `‖WithLp.ofLp q‖`; so the Bellman operator `bellman_op` acts on plain vectors
  `Fin _ → ℝ` and no `LinftySpace`/`toLinfty` casts are needed.
* `maxₐ q s = max_a q (s, a)`; `bellman_op q (s, a) = r (s, a) + γ ∑_{s'} P((s, a), {s'}) maxₐ q s'`.
* `optimal_q` is a fixed point of `bellman_op` (chosen with `Classical.epsilon`; its existence is
  the Banach fixed point theorem, proved as a lemma. rl: `ContractingWith.fixedPoint`).
* `update q ((s, a), (s', a')) = (r (s, a) + γ maxₐ q s' - q (s, a)) e_{(s, a)}`, with the SA
  residual forms `update_target` and `expected_update_target` as for linear TD.
* `μmin` = min of the stationary law, `η = 1 - μmin (1 - γ)` is the sup-norm contraction factor of
  `expected_update_target` (rl: `contraction_of_expected_update_target.choose`, made explicit), and
  `pmin = max 2 (⌈log |S × A| / log (1 / η)⌉₊ + 1)` the `ℓ^p` exponent of the Lyapunov function.
-/


-- Q-learning iterates driven by samples ω : ℕ → (S × A) × (S × A) (rl: `QLearning.QLearningIterates`)
class QLearningIterates {S : Type u} {A : Type v} [Fintype S] [DecidableEq S] [MeasurableSpace S]
    [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [Nonempty A] (spec : QLearningSpec S A)
    (q : ℕ → (ℕ → (S × A) × (S × A)) → EuclideanVec (Fintype.card (S × A))) : Prop where
  init : ∀ ω, q 0 ω = spec.q₀
  step : ∀ n ω, q (n + 1) ω = q n ω + spec.α n • spec.update (q n ω) (ω (n + 1))

