import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.TateShafarevich
open NumberField GaloisCohomology


/--
[GenusOneCurve.hasRationalPoint_iff_trivial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TateShafarevich.lean)
-/
@[path]
private lemma hasRationalPoint_iff_trivial_eq
  {k : Type u}
  [Field k]
  {C : GenusOneCurve k} :
-- imply
  C.HasRationalPoint ↔ C.wcClass = 0 := by
-- proof
  apply GenusOneCurve.hasRationalPoint_iff_trivial C

/--
[GenusOneCurve.hasLocalPoint_iff_localization_trivial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TateShafarevich.lean)
-/
@[path]
private lemma hasLocalPoint_iff_localization_trivial_eq
  {k : Type u}
  [Field k]
  [NumberField k]
  {C : GenusOneCurve k}
  {v : NumberFieldPlace k} :
-- imply
  C.HasLocalPoint v ↔ localizationMap C.Jacobian v C.wcClass = 0 := by
-- proof
  apply GenusOneCurve.hasLocalPoint_iff_localization_trivial C v

/--
[TateShafarevich.mem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TateShafarevich.lean)
-/
@[path]
private lemma mem_iff_eq
  {k : Type u}
  [Field k]
  [NumberField k]
  {E : EllipticCurveOver k}
  {x : WeilChateletGroup E} :
-- imply
  x ∈ TateShafarevich E ↔ ∀ v : NumberFieldPlace k, localizationMap E v x = 0 := by
-- proof
  apply TateShafarevich.mem_iff E x

/--
[GenusOneCurve.wcClass_mem_sha](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TateShafarevich.lean)
-/
@[path]
private lemma wcClass_mem_sha_eq
  {k : Type u}
  [Field k]
  [NumberField k]
  {C : GenusOneCurve k}
-- given
  (h : C.IsLocallyTrivial) :
-- imply
  C.wcClass ∈ TateShafarevich C.Jacobian := by
-- proof
  apply GenusOneCurve.wcClass_mem_sha C h

/--
[fails_local_global_iff_nontrivial_sha](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TateShafarevich.lean)
-/
@[path]
private lemma fails_local_global_iff_nontrivial_sha_eq
  {k : Type u}
  [Field k]
  [NumberField k]
  {C : GenusOneCurve k} :
-- imply
  FailsLocalGlobalPrinciple C ↔ (C.wcClass ∈ TateShafarevich C.Jacobian ∧ C.wcClass ≠ 0) := by
-- proof
  apply fails_local_global_iff_nontrivial_sha C


-- created on 2026-10-23
