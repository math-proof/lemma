import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingMarkovReflectionFold
open Finset StatMech StatMech.FrontierA


/--
[fkg_inequality_unnormalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingMarkovReflectionFold.lean)
-/
@[path]
private lemma fkg_inequality_unnormalized_eq
  [Fintype E]
  [DecidableEq E]
-- given
  (w : ConfigSpace E -> Real)
  (hwpos : forall omega, 0 < w omega)
  (hwFKG : FKGLatticeCondition w)
  (f g : ConfigSpace E -> Real)
  (hf : Monotone f)
  (hg : Monotone g) :
-- imply
  (∑ omega, w omega * f omega) * (∑ omega, w omega * g omega) <= (∑ omega, w omega) * ∑ omega, w omega * (f omega * g omega) := by
-- proof
  apply StatMech.FrontierA.fkg_inequality_unnormalized w hwpos hwFKG f g hf hg

/--
[markovReflectionFold_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingMarkovReflectionFold.lean)
-/
@[path]
private lemma markovReflectionFold_sum_le_eq
  [Fintype E]
  [DecidableEq E]
-- given
  (w : B -> ConfigSpace E -> Real)
  (hwpos : forall b omega, 0 < w b omega)
  (hwFKG : forall b, FKGLatticeCondition (w b))
  (f g : ConfigSpace E -> Real)
  (hf : Monotone f)
  (hg : Monotone g) :
-- imply
  (∑ b : B, ∑ lower : ConfigSpace E, ∑ upper : ConfigSpace E, (w b lower * w b upper) * (f lower * g upper)) <= ∑ b : B, ∑ lower : ConfigSpace E, ∑ upper : ConfigSpace E, (w b lower * w b upper) * (f lower * g lower) := by
-- proof
  apply StatMech.FrontierA.markovReflectionFold_sum_le w hwpos hwFKG f g hf hg


-- created on 2026-10-23
