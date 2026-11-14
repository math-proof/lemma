import Lemma.Random.All_EqProb_Cond.of.Indep
import Lemma.Random.Indep.Indep.of.IndepJoint
import Lemma.Random.SinglePSpace.of.IndepFun
open Random MeasureTheory ProbabilityTheory


/--
If the joint random variable `(x, y)` is independent of `z`, then each factor is
independent of `z` as well, written in observation form:
`(x, y) ⟂ᵢ[π] z` implies `ℙ(x | z) = ℙ(x)` and `ℙ(y | z) = ℙ(y)`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β] [ReferenceMeasure γ]
  {π : Measure Ω}
  {x : Ω → α} [SinglePSpace π x]
  {y : Ω → β} [SinglePSpace π y]
  {z : Ω → γ} [SinglePSpace π z]
-- given
  (h : (x, y) ⟂ᵢ[π] z) :
-- imply
  have : SinglePSpace π (x, z) :=
    SinglePSpace.of.IndepFun (Indep.Indep.of.IndepJoint h).left
  have : SinglePSpace π (y, z) :=
    SinglePSpace.of.IndepFun (Indep.Indep.of.IndepJoint h).right
  (∀ᵐ «\sf{x}» ∂ReferenceMeasure.measure,
    ∀ᵐ «\sf{z}» ∂π.map z,
      ℙ[π](x = «\sf{x}» | z = «\sf{z}») = ℙ[π](x = «\sf{x}»)) ∧
  (∀ᵐ «\sf{y}» ∂ReferenceMeasure.measure,
    ∀ᵐ «\sf{z}» ∂π.map z,
      ℙ[π](y = «\sf{y}» | z = «\sf{z}») = ℙ[π](y = «\sf{y}»)) :=
-- proof
  ⟨All_EqProb_Cond.of.Indep (Indep.Indep.of.IndepJoint h).left,
    All_EqProb_Cond.of.Indep (Indep.Indep.of.IndepJoint h).right⟩


-- created on 2023-03-23
-- updated on 2026-11-12
