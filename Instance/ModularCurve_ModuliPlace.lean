-- Carved from Lemma/Definitions/Def_ModularCurve_ModuliPlace.lean: instance decls only.
import Mathlib
import Lemma.HahnSeries.X0ModL
import Lemma.HahnSeries.QAdicPlaceMod
import Lemma.WeierstrassCurve.ModuliPointMap
import Lemma.WeierstrassCurve.ReduceHom
import Lemma.WeierstrassCurve.CyclicQuotientJ
import Lemma.Scheme.Correspondence
import Lemma.WeierstrassCurve.ModuliPlace

set_option autoImplicit false

noncomputable section

open IsLocalRing AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine

namespace ModularCurve

universe u


namespace ModuliTestDatum

variable {K : Type u} [Field K] [DecidableEq K] {N : ℕ} {x : ModuliPoint N K}

instance isElliptic_curve : D.curve.IsElliptic := ⟨D.isUnit_Δ⟩

instance isElliptic_generic : (D.curve.map D.W.toValuationSubring.subtype).IsElliptic :=
  inferInstance

instance isElliptic_reduced : (D.curve.map (residue D.W.toValuationSubring)).IsElliptic :=
  inferInstance


end ModuliTestDatum


end ModularCurve

end
