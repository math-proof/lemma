import Mathlib
import Lemma.AlgebraicCurve.Correspondence

set_option autoImplicit false

noncomputable section

open KaehlerDifferential TensorProduct

namespace AlgebraicCurve

namespace Differential

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

def pullbackAlong (φ : F →ₐ[K] F') : Ω[F⁄K] →ₗ[K] Ω[F'⁄K] :=
  let := algebraAlong φ
  have := isScalarTower_along φ
  (KaehlerDifferential.map K K F F').restrictScalars K


def traceAlong (φ : F →ₐ[K] F') : Ω[F'⁄K] →ₗ[K] Ω[F⁄K] :=
  if h : SeparableAlong K φ then
    let := algebraAlong φ
    have := isScalarTower_along φ
    have : Algebra.IsSeparable F F' := h
    have : Algebra.FormallyEtale F F' := Algebra.FormallyEtale.of_isSeparable F F'
    ((TensorProduct.lid F Ω[F⁄K]).toLinearMap ∘ₗ
      (Algebra.trace F F').rTensor Ω[F⁄K] ∘ₗ
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F F').symm.toLinearMap).restrictScalars K
  else 0


def correspondence (φ ψ : F →ₐ[K] F') : Ω[F⁄K] →ₗ[K] Ω[F⁄K] :=
  traceAlong φ ∘ₗ pullbackAlong ψ


end Differential

end AlgebraicCurve

end
