import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Probability.Independence.Basic
import sympy.stats.symbolic_probability
open MeasureTheory


/--
[sympy.JointRandomSymbol](https://github.com/sympy/sympy/blob/master/sympy/stats/joint_rv.py)
-/
def JointRandomSymbol
    {Ω α β : Type*}
    (x : Ω → α) (y : Ω → β) :
    Ω → α × β :=
  fun ω ↦ (x ω, y ω)


/--
Pointwise coercion of a pair of functions on the same domain to a function into pairs:
`↑(x, y) = JointRandomSymbol x y`. A bare pair `(x, y)` is therefore accepted
wherever an `Ω → α × β` is expected — e.g. `let prod : Ω → α × β := (x, y)` — and the
`CoeFun` instance also makes application `(x, y) ω` well-typed. The coe body delegates
to `JointRandomSymbol` (rather than re-using an anonymous `fun`) so typeclass search
sees the same head symbol: e.g. a hypothesis written as a bare pair `(x, y)`
also supplies `PSpace 𝕡 (x, y)`.
-/
instance Function.coeProdPi {ι α β : Type*} :
    Coe ((ι → α) × (ι → β)) (ι → α × β) :=
  ⟨fun p ↦ JointRandomSymbol p.1 p.2⟩

instance Function.coeFunProdPi {ι α β : Type*} :
    CoeFun ((ι → α) × (ι → β)) (fun _ => ι → α × β) :=
  ⟨fun p ↦ JointRandomSymbol p.1 p.2⟩


/--
Triple variants: a nested pair of functions on the same domain coerces in one step to a
function into nested pairs, in both associations. Coercions do not chain through nested
`Prod.mk` nodes at argument positions, so a bare `((x, y), z)` or `(x, (y, z))` needs these
instances to be accepted where an `Ω → (α × β) × γ` (resp. `Ω → α × (β × γ)`) is expected.
-/
instance Function.coeProdPi3L {ι α β γ : Type*} :
    Coe (((ι → α) × (ι → β)) × (ι → γ)) (ι → (α × β) × γ) :=
  ⟨fun p ↦ JointRandomSymbol (JointRandomSymbol p.1.1 p.1.2) p.2⟩

instance Function.coeProdPi3R {ι α β γ : Type*} :
    Coe ((ι → α) × ((ι → β) × (ι → γ))) (ι → α × (β × γ)) :=
  ⟨fun p ↦ JointRandomSymbol p.1 (JointRandomSymbol p.2.1 p.2.2)⟩

instance Function.coeFunProdPi3L {ι α β γ : Type*} :
    CoeFun (((ι → α) × (ι → β)) × (ι → γ)) (fun _ => ι → (α × β) × γ) :=
  ⟨fun p ↦ JointRandomSymbol (JointRandomSymbol p.1.1 p.1.2) p.2⟩

instance Function.coeFunProdPi3R {ι α β γ : Type*} :
    CoeFun ((ι → α) × ((ι → β) × (ι → γ))) (fun _ => ι → α × (β × γ)) :=
  ⟨fun p ↦ JointRandomSymbol p.1 (JointRandomSymbol p.2.1 p.2.2)⟩


/--
Build a joint `PSpace 𝕡 (x, y)` from an explicit density `p` of the joint law: if
`𝕡.map (x, y)` equals the product reference measure with density `p`, then `(x, y)` admits
`p` as its distribution. The a.e. measurability of the pair is supplied directly.
-/
theorem JointRandomSymbol.of_density
    {Ω α β : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure β]
    {𝕡 : Measure Ω}
    {x : Ω → α} {y : Ω → β} [IsProbabilityMeasure 𝕡]
    {p : α × β → ENNReal}
    (hxy : AEMeasurable (x, y) 𝕡)
    (hp : Measurable p)
    (hjoint : 𝕡.map (x, y) =
      (ReferenceMeasure.measure.prod ReferenceMeasure.measure).withDensity p) :
    PSpace 𝕡 (x, y) :=
  { toIsProbabilityMeasure := inferInstance
    aemeasurable := hxy
    exists_distribution := ⟨p, ⟨hp⟩, hjoint⟩ }


/--
Two random variables whose laws each admit a density (`PSpace 𝕡 x` and
`PSpace 𝕡 y`) also span a **joint** probability space with density when they are
independent: by `IndepFun`, the joint law is the product of the marginal laws, and the
product of two measures with densities `px`, `py` is the product measure with density
`fun z ↦ px z.1 * py z.2`. The a.e. measurability of `x` and `y` needed by `IndepFun` is
read off the `PSpace` instances (which package `AEMeasurable`); plain `Measurable`
hypotheses are not required. The converse is false without independence — two ac
marginals can have a singular joint law (e.g. `y = x` over a Lebesgue state space).
-/
theorem JointRandomSymbol.of_indep
    {Ω α β : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure β]
    {𝕡 : Measure Ω}
    {x : Ω → α} {y : Ω → β}
    [PSpace 𝕡 x] [PSpace 𝕡 y]
    (hxy : ProbabilityTheory.IndepFun x y 𝕡) :
    PSpace 𝕡 (x, y) := by
  let μ : Measure α := ReferenceMeasure.measure
  let ν : Measure β := ReferenceMeasure.measure
  let px := 𝕡.prob x
  let py := 𝕡.prob y
  let p : α × β → ENNReal := fun z ↦ px z.1 * py z.2
  have hpx : Measurable px := Measure.measurable_rnDeriv _ _
  have hpy : Measurable py := Measure.measurable_rnDeriv _ _
  have hp : Measurable p :=
    (hpx.comp measurable_fst).mul (hpy.comp measurable_snd)
  have haex : AEMeasurable x 𝕡 := PSpace.aemeasurable
  have haey : AEMeasurable y 𝕡 := PSpace.aemeasurable
  have hindep : 𝕡.map (x, y) = (𝕡.map x).prod (𝕡.map y) :=
    ProbabilityTheory.IndepFun.map_prod_eq_prod_map_map haex haey hxy
  have hjoint : 𝕡.map (x, y) = (μ.prod ν).withDensity p := by
    rw [hindep, PSpace.map_eq_withDensity_density,
      PSpace.map_eq_withDensity_density, prod_withDensity hpx hpy]
  exact JointRandomSymbol.of_density (haex.prodMk haey) hp hjoint
