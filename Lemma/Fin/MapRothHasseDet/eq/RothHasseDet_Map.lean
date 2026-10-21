import Mathlib
import Lemma.Fin.MapRothMvHasse.eq.RothMvHasse_Map.of.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothHasseDet_map](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m k : ℕ} [CommRing R] [CommRing S]
  (f : R →+* S)
  (P : MvPolynomial (Fin m) R) (u v : Fin k → RothMvIndex m) :
-- imply
  MvPolynomial.map f (rothHasseDet P u v) =
    rothHasseDet (MvPolynomial.map f P) u v := by
-- proof
  classical
  let M : Matrix (Fin k) (Fin k) (MvPolynomial (Fin m) R) :=
    fun s t ↦ rothMvHasse (u s + v t) P
  unfold rothHasseDet
  change MvPolynomial.map f M.det = _
  rw [RingHom.map_det]
  congr 1
  funext s t
  exact MapRothMvHasse.eq.RothMvHasse_Map.of.RothMvIndex f (u s + v t) P


-- created on 2026-10-21
