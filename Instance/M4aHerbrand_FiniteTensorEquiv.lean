-- Carved from Lemma/Definitions/Def_M4aHerbrand_FiniteTensorEquiv.lean: instance decls only.
import Mathlib.RingTheory.Flat.TorsionFree

noncomputable section

namespace M4aHerbrand.Bridge

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum TensorProduct RestrictedProduct

open scoped TensorProduct RestrictedProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3

section AKLB

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [Algebra.IsIntegral A B] [IsFractionRing B L] [IsDedekindDomain B]
    [FiniteDimensional K L] [Module.Finite A B]

section shortcut_instances

variable (v : HeightOneSpectrum A) (w' : HeightOneSpectrum B)

private instance : IsUniformAddGroup (WithVal (v.valuation K)) := inferInstance
private noncomputable instance : AddCommGroup (v.adicCompletion K) := inferInstance
private noncomputable instance : AddCommMonoid (v.adicCompletion K) := inferInstance
private noncomputable instance : CommRing (v.adicCompletion K) := inferInstance
private noncomputable instance : Ring (v.adicCompletion K) := inferInstance
private noncomputable instance : Module A (v.adicCompletion K) := inferInstance
private noncomputable instance : AddCommGroup (B ⊗[A] v.adicCompletion K) := inferInstance
private noncomputable instance : AddCommMonoid (B ⊗[A] v.adicCompletion K) := inferInstance
private noncomputable instance : CommRing (B ⊗[A] v.adicCompletion K) := inferInstance
private noncomputable instance : Module B (B ⊗[A] v.adicCompletion K) := inferInstance
private instance : IsUniformAddGroup (WithVal (w'.valuation L)) := inferInstance
private noncomputable instance : AddCommGroup (w'.adicCompletion L) := inferInstance
private noncomputable instance : AddCommMonoid (w'.adicCompletion L) := inferInstance
private noncomputable instance : CommRing (w'.adicCompletion L) := inferInstance
private noncomputable instance : Ring (w'.adicCompletion L) := inferInstance
private noncomputable instance : AddCommGroup ((w : v.Extension B) → w.1.adicCompletion L) := inferInstance
private noncomputable instance : AddCommMonoid ((w : v.Extension B) → w.1.adicCompletion L) := inferInstance
private noncomputable instance : CommRing ((w : v.Extension B) → w.1.adicCompletion L) := inferInstance
private noncomputable instance : Module B ((w : v.Extension B) → w.1.adicCompletion L) := inferInstance

end shortcut_instances


end AKLB

end M4aHerbrand.Bridge

end
