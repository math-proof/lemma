import Instance.GoodReductionJacobian_RelativeGroupLawAlgPointsV2
import Instance.EllipticCurve_TateModule

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.RiemannForm

variable {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))

abbrev Pt : Type := SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k))) f

end AlgebraicGeometry.RiemannForm

end
