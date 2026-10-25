-- Carved from Lemma/Definitions/Def_CerednikDrinfeld_DrinfeldUpperHalfPlane.lean: instance decls only.
import Mathlib
import Lemma.CerednikDrinfeld.DrinfeldUpperHalfPlane

set_option autoImplicit false

open scoped MatrixGroups Topology

namespace CerednikDrinfeld
namespace Omega

section Moebius

variable (K₀ : Type*) [Field K₀] (K : Type*) [Field K] [Algebra K₀ K]

noncomputable scoped instance (priority := low) glAction [DecidableEq K] : MulAction (GL (Fin 2) K₀) (OnePoint K) :=
  MulAction.compHom (OnePoint K) (Matrix.GeneralLinearGroup.map (algebraMap K₀ K))

noncomputable scoped instance (priority := low) pglAction [DecidableEq K] : MulAction PGL(2, K₀) (OnePoint K) :=
  Matrix.ProjGenLinGroup.mulActionOfGL (fun u x => scalar_smul_eq K₀ K u x)

end Moebius


end Omega
end CerednikDrinfeld
