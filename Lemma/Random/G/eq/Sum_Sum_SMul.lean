import sympy.stats.markov_samples
import sympy.Basic
import Lemma.Matrix.Sum_Mul.eq.One.of.StochasticVec.RowStochastic
open Finset


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {d : ℕ}
  {sk : Skeleton S d}
-- given
  (w : EuclideanVec d) :
-- imply
  sk.g w = ∑ s, ∑ s', (sk.mrp.μ s * sk.mrp.P s s') • sk.G w (s, s') := by
-- proof
  simp only [Skeleton.g, Skeleton.G, Pi.sub_apply, id, smul_sub, sum_sub_distrib, ← sum_smul, sk.hfF,
    Matrix.Sum_Mul.eq.One.of.StochasticVec.RowStochastic (inferInstance : RowStochastic sk.mrp.P) (inferInstance : StochasticVec sk.mrp.μ), one_smul]


-- created on 2026-09-26