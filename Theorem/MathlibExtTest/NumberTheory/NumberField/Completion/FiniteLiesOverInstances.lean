/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/Completion/FiniteLiesOverInstances.lean -/


import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Instance.NumberTheory.NumberField.Completion.FiniteLiesOverInstances
open IsDedekindDomain.HeightOneSpectrum
open scoped NumberField
open scoped NumberField.LiesOver

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]
variable {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)}
variable {w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)}
variable [w.asIdeal.LiesOver v.asIdeal]

/-!
# Tests for finite-place completion instances

Generic checks that the scoped `NumberField.LiesOver` instances for finite-place
completions infer correctly and integrate with `Module.Finite`.
-/


noncomputable section

example : Algebra (v.adicCompletion K) (w.adicCompletion L) := inferInstance

example : algebraMap (v.adicCompletion K) (w.adicCompletion L) =
    adicCompletionMap v w :=
  RingHom.algebraMap_toAlgebra (adicCompletionMap v w)

example (x : K) : algebraMap (v.adicCompletion K) (w.adicCompletion L)
    (algebraMap K (v.adicCompletion K) x) = algebraMap K (w.adicCompletion L) x :=
  (IsScalarTower.algebraMap_apply K (v.adicCompletion K) (w.adicCompletion L) x).symm

example : ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) := inferInstance

example : Continuous (algebraMap (v.adicCompletion K) (w.adicCompletion L)) :=
  continuous_algebraMap _ _

example : Module.Finite (v.adicCompletion K) (w.adicCompletion L) := inferInstance

end
