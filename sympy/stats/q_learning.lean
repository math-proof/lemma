import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import sympy.stats.markov_decision_process
import sympy.vector.euclidean

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
open Finset

universe u v

-- tabular Q-learning on a finite MDP (rl: `ReinforcementLearning.QLearning.QLearningSpec`)
structure QLearningSpec (S : Type u) (A : Type v) [Fintype S] [DecidableEq S] [MeasurableSpace S]
    [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] [MeasurableSpace A]
    [MeasurableSingletonClass A] extends FiniteMDP S A where
  α : ℕ → ℝ
  q₀ : EuclideanVec (Fintype.card (S × A))

namespace QLearningSpec

variable {S : Type u} {A : Type v} [Fintype S] [DecidableEq S] [MeasurableSpace S]
  [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] [MeasurableSpace A]
  [MeasurableSingletonClass A]

-- the enumeration of state-action pairs (rl: `QLearning.sa_to_fin`)
noncomputable def sa_to_fin (y : S × A) : Fin (Fintype.card (S × A)) :=
  Fintype.equivFin (S × A) y

-- its inverse (rl: `QLearning.fin_to_sa`)
noncomputable def fin_to_sa (i : Fin (Fintype.card (S × A))) : S × A :=
  (Fintype.equivFin (S × A)).symm i

-- the indicator vector of a state-action pair (rl: `QLearningSpec.x`)
noncomputable def x (y : S × A) : EuclideanVec (Fintype.card (S × A)) :=
  EuclideanSpace.single (sa_to_fin y) 1

section greedy

variable [Nonempty A]

-- max over actions of a Q-table (rl: `QLearningSpec.maxₐ`)
noncomputable def maxₐ (q : Fin (Fintype.card (S × A)) → ℝ) (s : S) : ℝ :=
  univ.sup' univ_nonempty fun a => q (sa_to_fin (s, a))

variable (spec : QLearningSpec S A)

-- the Bellman optimality operator on plain Q-tables (rl: `QLearningSpec.bellman_op`)
noncomputable def bellman_op (q : Fin (Fintype.card (S × A)) → ℝ) : Fin (Fintype.card (S × A)) → ℝ :=
  fun i => spec.r (fin_to_sa i) + spec.γ * ∑ s', (spec.P (fin_to_sa i) {s'} : ℝ) * maxₐ q s'

-- a fixed point of the Bellman operator (rl: `QLearningSpec.optimal_q`)
noncomputable def optimal_q : EuclideanVec (Fintype.card (S × A)) :=
  WithLp.toLp 2 (Classical.epsilon fun q => spec.bellman_op q = q)

-- the Q-learning update direction (rl: `QLearningSpec.update`)
noncomputable def update (q : EuclideanVec (Fintype.card (S × A))) (y : (S × A) × (S × A)) :
    EuclideanVec (Fintype.card (S × A)) :=
  (spec.r y.1 + spec.γ * maxₐ (WithLp.ofLp q) y.2.1 - q (sa_to_fin y.1)) • x y.1

-- the SA residual form F q y = update q y + q (rl: `QLearningSpec.update_target`)
noncomputable def update_target (q : EuclideanVec (Fintype.card (S × A))) (y : (S × A) × (S × A)) :
    EuclideanVec (Fintype.card (S × A)) :=
  spec.update q y + q

section stationary

variable [Nonempty S]

-- the mean update under the stationary pair law of the induced chain (rl: `QLearningSpec.expected_update`)
noncomputable def expected_update (q : EuclideanVec (Fintype.card (S × A))) : EuclideanVec (Fintype.card (S × A)) :=
  ∑ y, ∑ y', (spec.MRP.μ y * spec.MRP.P y y') • spec.update q (y, y')

-- f = expected_update + id (rl: `QLearningSpec.expected_update_target`)
noncomputable def expected_update_target : EuclideanVec (Fintype.card (S × A)) → EuclideanVec (Fintype.card (S × A)) :=
  spec.expected_update + id

-- the smallest stationary probability (rl: `μmin`, local to `contraction_of_expected_update_target`)
noncomputable def μmin : ℝ :=
  univ.inf' univ_nonempty spec.MRP.μ

-- the sup-norm contraction factor of `expected_update_target` (rl: `contraction_of_expected_update_target.choose`)
noncomputable def η : ℝ :=
  1 - spec.μmin * (1 - spec.γ)

-- log |S × A| / log (1 / η) (rl: `QLearningSpec.pmin_aux`, written `1 / (log (1 / η) / log |S × A|)`)
noncomputable def pmin_aux : ℝ :=
  Real.log (Fintype.card (S × A)) / Real.log (1 / spec.η)

-- the ℓ^p exponent of the Lyapunov function (rl: `QLearningSpec.pmin`)
noncomputable def pmin : ℕ :=
  max 2 (⌈spec.pmin_aux⌉₊ + 1)

end stationary

end greedy

end QLearningSpec

-- Q-learning iterates driven by samples ω : ℕ → (S × A) × (S × A) (rl: `QLearning.QLearningIterates`)
class QLearningIterates {S : Type u} {A : Type v} [Fintype S] [DecidableEq S] [MeasurableSpace S]
    [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [Nonempty A] (spec : QLearningSpec S A)
    (q : ℕ → (ℕ → (S × A) × (S × A)) → EuclideanVec (Fintype.card (S × A))) : Prop where
  init : ∀ ω, q 0 ω = spec.q₀
  step : ∀ n ω, q (n + 1) ω = q n ω + spec.α n • spec.update (q n ω) (ω (n + 1))