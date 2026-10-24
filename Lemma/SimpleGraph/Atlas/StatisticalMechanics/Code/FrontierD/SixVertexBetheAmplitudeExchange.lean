import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheAmplitudeExchange
open Finset StatMech StatMech.FrontierD


/--
[sixVertexBetheAmplitude_adjacent_exchange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAmplitudeExchange.lean)
-/
@[path]
private lemma sixVertexBetheAmplitude_adjacent_exchange_eq
  {c : ℝ}
  {n : ℕ}
  {p : Fin (n + 1) → ℝ}
  {σ : Equiv.Perm (Fin (n + 1))}
  {i : Fin n}
-- given
  (hc : 2 < c) :
-- imply
  Complex.exp (-Complex.I * sixVertexTheta c (p (σ i.castSucc)) (p (σ i.succ))) * sixVertexBetheAmplitude c p (σ * Equiv.swap i.castSucc i.succ) = -sixVertexBetheAmplitude c p σ := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheAmplitude_adjacent_exchange hc p σ i

/--
[SixVertexSatisfiesMultiplicativeBetheEquations.amplitude_rotate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAmplitudeExchange.lean)
-/
@[path]
private lemma amplitude_rotate_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin (n + 1) → ℝ}
  {σ : Equiv.Perm (Fin (n + 1))}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p) :
-- imply
  sixVertexBethePhase (p (σ 0)) ^ N * sixVertexBetheAmplitude c p (σ * finRotate (n + 1)) = sixVertexBetheAmplitude c p σ := by
-- proof
  apply StatMech.FrontierD.SixVertexSatisfiesMultiplicativeBetheEquations.amplitude_rotate hc hp σ

/--
[SixVertexSatisfiesMultiplicativeBetheEquations.amplitude_boundary_exchange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAmplitudeExchange.lean)
-/
@[path]
private lemma amplitude_boundary_exchange_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin (n + 2) → ℝ}
  {σ : Equiv.Perm (Fin (n + 2))}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p) :
-- imply
  Complex.exp (-Complex.I * sixVertexTheta c (p (σ (Fin.last (n + 1)))) (p (σ 0))) * sixVertexBethePhase (p (σ 0)) ^ N * sixVertexBetheAmplitude c p (σ * ((finRotate (n + 2)).symm * Equiv.swap 0 1 * finRotate (n + 2))) = -(sixVertexBethePhase (p (σ (Fin.last (n + 1)))) ^ N * sixVertexBetheAmplitude c p σ) := by
-- proof
  apply StatMech.FrontierD.SixVertexSatisfiesMultiplicativeBetheEquations.amplitude_boundary_exchange hc hp σ


-- created on 2026-10-23
