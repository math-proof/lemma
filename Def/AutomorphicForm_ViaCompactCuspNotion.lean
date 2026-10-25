import Lemma.AutomorphicForm.ArithCuspRealization
import Def.AutomorphicForm_ProductionPinsCompact
import Lemma.AutomorphicForm.ArchWeightCharTransport
import Def.ModularForm_EisensteinChiNegThree

set_option autoImplicit false

open IsDedekindDomain NumberField EisensteinWeightOne CongruenceSubgroup
open scoped Manifold

noncomputable section

namespace AutomorphicForm

def iotaZsqrtdNegTwo : ℤ√(-2) →+* ℂ :=
  Zsqrtd.lift ⟨(Real.sqrt 2 : ℂ) * Complex.I, by
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
      rw [← Complex.ofReal_mul, ← Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2)]
      norm_num [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2)]
    calc ((Real.sqrt 2 : ℂ) * Complex.I) * ((Real.sqrt 2 : ℂ) * Complex.I)
        = (((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ)) * (Complex.I * Complex.I) := by
          ring
      _ = ((-2 : ℤ) : ℂ) := by rw [h2, Complex.I_mul_I]; norm_num⟩


noncomputable def iwasawaSectionGL (z : UpperHalfPlane) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(z.im : ℝ), (z.re : ℝ); 0, 1] (by
    simp [Matrix.det_fin_two_of]
    exact z.im_ne_zero)

def IsArchHolomorphicAt {F : Type} [Field F] [NumberField F] (w : InfinitePlace F)
    (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ g : AdelicGL2 (𝓞 F) F, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : UpperHalfPlane =>
    ((z.im : ℝ) : ℂ)⁻¹ * φ (g * adelicArchGLInclAt F w
      (Matrix.GeneralLinearGroup.map
        ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
        (iwasawaSectionGL z)))

def viaCompactCuspNotion : CuspidalityNotion (ℤ√(-2)) where
  IsCusp := fun F _i1 _i2 Φ =>
    (∃ R : SmoothCuspRealizationAt F (productionPinsCompact F)
        ((Φ.map iotaZsqrtdNegTwo).toRawCentral),
      (∀ w : InfinitePlace F, ∀ hw : w.IsReal,
        HasArchCharacterAt₀ F w (archWeightOneAt hw) R.toFun) ∧
      (∀ w : InfinitePlace F, ∀ hw : w.IsReal,
        IsArchHolomorphicAt w hw R.toFun)) ∧
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S,
      Φ.b v = ((chiNegThree (Ideal.absNorm v.asIdeal) : ℤ) : ℤ√(-2))

end AutomorphicForm

end
