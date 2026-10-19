import Lemma.Random.EqW
import Lemma.Random.Pn.eq.Integral
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
`Pn θ 0 x y = 1{x = y}`: the `0`-step state transition of the trajectory model `M` is the identity.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
-- given
  (θ : Θ)
  (x y : S) :
-- imply
  M.Pn θ 0 x y = if x = y then 1 else 0 :=
  Pn.eq.Integral (M := M) θ 0 x y ▸
    Random.EqW (M := M) θ (fun x' => if x' = y then (1:ℝ) else 0) x


-- created on 2026-10-06
