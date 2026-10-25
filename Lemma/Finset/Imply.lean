import Mathlib
import sympy.Basic
import Lemma.WeierstrassCurve.VeluQuotientMap
open WeierstrassCurve


/--
IsOddVeluSet implies IsVeluSet (Finset kernel set for Velu).
Source retirement from Def_WeierstrassCurve_VeluQuotientMap.
-/
@[path]
private lemma main
  [CommRing R]
  {W : WeierstrassCurve R}
  {S : Finset (R × R)}
-- given
  (h : W.IsOddVeluSet S) :
-- imply
  W.IsVeluSet S :=
-- proof
  ⟨h.equation⟩


-- created on 2026-10-24
