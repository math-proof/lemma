import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_FormalGroup_DrinfeldBasis
import Lemma.Definitions.Def_FormalGroup_NSeries
import Lemma.Definitions.Def_FormalGroup_PointTransport
open FormalGroup IsLocalRing


/-- ported from external source -/
@[path]
private lemma main
  [CommRing R] [CommRing S]
  {F : FormalGroup R}
  {f : R →+* S} :
-- imply
  ∃ G : FormalGroup S, F.IsBaseChange f G :=
  ⟨F.map f, rfl⟩


-- created on 2026-10-23
