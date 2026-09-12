import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Probability.Independence.Basic
import sympy.stats.symbolic_probability
open MeasureTheory


/--
[sympy.JointPSpace](https://github.com/sympy/sympy/blob/master/sympy/stats/joint_rv.py)

The joint probability space of the random variables `x` and `y`. Mirroring sympy's
inheritance `JointPSpace(ProductPSpace(PSpace))`, it is a `PSpace` for the **single** joint
random variable `ω ↦ (x ω, y ω) : Ω → α × β` — `x` and `y` bundled together as one random
variable (whose state measure is the product of the canonical state measures on `α` and
`β`): this joint RV follows a distribution `D : Distribution 𝕡 π` (`~`), i.e. the joint
law equals the product state measure with density `π` (`Pr(x, y)` in sympy notation).

Being a `PSpace`, it also packages that `𝕡` is a probability measure (so
`[IsProbabilityMeasure 𝕡]` need not be stated separately once a `JointPSpace` instance is
in scope).

The density itself is not a separate hypothesis; it is recovered as
`JointPSpace.density 𝕡 x y` (a.e.). The probability of an event is
`JointPSpace.probability`.
-/
class JointPSpace
    {Ω α β : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure β]
    (𝕡 : Measure Ω)
    (x : Ω → α) (y : Ω → β) :
    Prop extends
    PSpace 𝕡 (fun ω ↦ (x ω, y ω)) where


/--
[sympy.JointPSpace.probability](https://github.com/sympy/sympy/blob/master/sympy/stats/joint_rv.py)

Joint probability of an event: the usual definition of (joint) probability as a function
of a condition. `JointPSpace.probability 𝕡 x y s` is the probability that the joint random
variable `ω ↦ (x ω, y ω)` takes a value in the event `s : Set (α × β)` — the value of the
joint law at `s` — and is a non-negative scalar (`ENNReal`, at most `1` since `𝕡` is a
probability measure):

  `JointPSpace.probability 𝕡 x y s = 𝕡.map (fun ω ↦ (x ω, y ω)) s`

For a measurable event this equals `𝕡 {ω | (x ω, y ω) ∈ s}` (`Measure.map_apply`);
a point condition is written as a set, e.g. `{p | p.1 = a ∧ p.2 = b}` in the discrete case.
-/
noncomputable def JointPSpace.probability
    {Ω α β : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure β]
    (𝕡 : Measure Ω)
    (x : Ω → α) (y : Ω → β)
    [JointPSpace 𝕡 x y]
    (s : Set (α × β)) :
    ENNReal :=
  𝕡.map (fun ω ↦ (x ω, y ω)) s


/--
A marginal of a joint probability space admitting a density also admits a density: if
`JointPSpace 𝕡 x y` holds, then `PSpace 𝕡 x` holds. The marginal density is the
section integral `q a = ∫⁻ b, p (a, b) ∂ReferenceMeasure.measure` (Tonelli's theorem), and
`𝕡.map x = ReferenceMeasure.measure.withDensity q`.
-/
theorem PSpace.ofJointPSpace
    {Ω α β : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure β]
    {𝕡 : Measure Ω}
    {x : Ω → α} {y : Ω → β}
    (hP : JointPSpace 𝕡 x y)
    (hx : Measurable x)
    (hy : Measurable y) :
    PSpace 𝕡 x := by
  let μ : Measure α := ReferenceMeasure.measure
  let ν : Measure β := ReferenceMeasure.measure
  obtain ⟨p, D, hjoint⟩ := hP.exists_distribution
  have hp : Measurable p := D.measurable_density
  let q : α → ENNReal := fun a ↦ lintegral ν (fun b ↦ p (a, b))
  have hq : Measurable q := hp.lintegral_prod_right'
  have hmap : 𝕡.map x =
      (𝕡.map (fun ω ↦ (x ω, y ω))).map Prod.fst :=
    (Measure.map_map measurable_fst
      (by fun_prop : Measurable (fun ω ↦ (x ω, y ω)))).symm
  have hlaw : 𝕡.map x = μ.withDensity q := by
    have hjoint : 𝕡.map (fun ω ↦ (x ω, y ω)) = (μ.prod ν).withDensity p := hjoint
    rw [hmap, hjoint]
    have hmarg :
        μ.withDensity (fun a ↦ lintegral ν (fun b ↦ p (a, b))) =
          ((μ.prod ν).withDensity p).fst := by
      ext s hs
      rw [withDensity_apply _ hs]
      have h : ((μ.prod ν).withDensity p).fst s =
          lintegral (μ.restrict s) (fun a ↦ lintegral ν (fun b ↦ p (a, b))) := by
        rw [Measure.fst_apply hs, ← Set.prod_univ,
          withDensity_apply _ (MeasurableSet.prod hs MeasurableSet.univ),
          setLIntegral_prod p (hp.aemeasurable.restrict)]
        simp only [setLIntegral_univ]
      exact h.symm
    exact hmarg.symm
  exact { toIsProbabilityMeasure := inferInstance
          exists_distribution := ⟨q, ⟨hq⟩, hlaw⟩ }


/--
Canonical joint density `Pr(x, y)` (Radon–Nikodym derivative of the joint law).
Equal a.e. to any witnessing density from `JointPSpace.exists_distribution`.
-/
noncomputable def JointPSpace.density
    {Ω α β : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure β]
    (𝕡 : Measure Ω)
    (x : Ω → α) (y : Ω → β)
    [JointPSpace 𝕡 x y] :
    α × β → ENNReal :=
  (𝕡.map (fun ω ↦ (x ω, y ω))).rnDeriv
    (ReferenceMeasure.measure.prod ReferenceMeasure.measure)


/--
Marginal density `Pr(y)` of `y`: Radon–Nikodym derivative of the law of `y` with respect
to the canonical state measure on `β`.
Equal a.e. to `fun b ↦ ∫⁻ a, JointPSpace.density 𝕡 x y (a, b) ∂μ` (the marginal law
projected from the joint density).
-/
noncomputable def JointPSpace.marginalDensity
    {Ω α β : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure β]
    (𝕡 : Measure Ω)
    (x : Ω → α) (y : Ω → β)
    [JointPSpace 𝕡 x y] :
    β → ENNReal :=
  (𝕡.map y).rnDeriv ReferenceMeasure.measure


/--
Conditional density `Pr(x | y)` of `x` given `y`.

When the joint law admits the density `Pr(x, y)`, the conditional density at `(a, b)` is
the joint density at `(a, b)` divided by the marginal density of `y` at `b` — the Bayes
formula `Pr(x | y) = Pr(x, y) / Pr(y)`. The quotient is the total `ENNReal` division, so it
is well-defined everywhere (it is `0` off the support of the marginal, where the conditional
law is irrelevant); see `Random.Pr.eq.DivPrS` for the a.e. identity with the explicit
marginal integral.
-/
noncomputable def JointPSpace.condDensity
    {Ω α β : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure β]
    (𝕡 : Measure Ω)
    (x : Ω → α) (y : Ω → β)
    [JointPSpace 𝕡 x y] :
    α × β → ENNReal :=
  fun z ↦ JointPSpace.density 𝕡 x y z /
    JointPSpace.marginalDensity 𝕡 x y z.2


/--
Build the `JointPSpace` instance from an explicit density `p`,
its measurability, and the joint-law equation w.r.t. the state measures, e.g.
`have hP : JointPSpace 𝕡 x y := JointPSpace.of_density hp hjoint`.
-/
theorem JointPSpace.of_density
    {Ω α β : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure β]
    {𝕡 : Measure Ω}
    {x : Ω → α} {y : Ω → β} [IsProbabilityMeasure 𝕡]
    {p : α × β → ENNReal}
    (hp : Measurable p)
    (hjoint : 𝕡.map (fun ω ↦ (x ω, y ω)) =
      (ReferenceMeasure.measure.prod ReferenceMeasure.measure).withDensity p) :
    JointPSpace 𝕡 x y where
  toPSpace :=
    { toIsProbabilityMeasure := inferInstance
      exists_distribution := ⟨p, ⟨hp⟩, hjoint⟩ }


/--
The joint law of `x` and `y` equals the product state measure with density
`JointPSpace.density 𝕡 x y` (`PSpace.map_eq_withDensity_density` for two
variables).
-/
theorem JointPSpace.map_eq_withDensity_density
    {Ω α β : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure β]
    {𝕡 : Measure Ω}
    {x : Ω → α} {y : Ω → β}
    [JointPSpace 𝕡 x y] :
    𝕡.map (fun ω ↦ (x ω, y ω)) =
      (ReferenceMeasure.measure.prod ReferenceMeasure.measure).withDensity
        (JointPSpace.density 𝕡 x y) := by
  have hp : JointPSpace 𝕡 x y := inferInstance
  obtain ⟨_, _, hlaw⟩ := hp.exists_distribution
  exact (Measure.withDensity_rnDeriv_eq (𝕡.map (fun ω ↦ (x ω, y ω))) _
    (hlaw ▸ withDensity_absolutelyContinuous _ _)).symm


/--
Two random variables whose laws each admit a density (`PSpace 𝕡 x` and
`PSpace 𝕡 y`) also span a **joint** probability space with density when they are
independent: by `IndepFun`, the joint law is the product of the marginal laws, and the
product of two measures with densities `px`, `py` is the product measure with density
`fun z ↦ px z.1 * py z.2`. The converse is false without independence — two ac marginals
can have a singular joint law (e.g. `y = x` over a Lebesgue state space).
-/
theorem JointPSpace.of_indep
    {Ω α β : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure β]
    {𝕡 : Measure Ω}
    {x : Ω → α} {y : Ω → β}
    [PSpace 𝕡 x] [PSpace 𝕡 y]
    (hx : Measurable x)
    (hy : Measurable y)
    (hxy : ProbabilityTheory.IndepFun x y 𝕡) :
    JointPSpace 𝕡 x y := by
  let μ : Measure α := ReferenceMeasure.measure
  let ν : Measure β := ReferenceMeasure.measure
  let px := PSpace.density 𝕡 x
  let py := PSpace.density 𝕡 y
  let p : α × β → ENNReal := fun z ↦ px z.1 * py z.2
  have hpx : Measurable px := Measure.measurable_rnDeriv _ _
  have hpy : Measurable py := Measure.measurable_rnDeriv _ _
  have hp : Measurable p :=
    (hpx.comp measurable_fst).mul (hpy.comp measurable_snd)
  have hindep : 𝕡.map (fun ω ↦ (x ω, y ω)) =
      (𝕡.map x).prod (𝕡.map y) :=
    ProbabilityTheory.IndepFun.map_prod_eq_prod_map_map
      hx.aemeasurable hy.aemeasurable hxy
  have hjoint : 𝕡.map (fun ω ↦ (x ω, y ω)) = (μ.prod ν).withDensity p := by
    rw [hindep, PSpace.map_eq_withDensity_density,
      PSpace.map_eq_withDensity_density, prod_withDensity hpx hpy]
  exact JointPSpace.of_density hp hjoint
