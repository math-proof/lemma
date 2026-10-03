import Mathlib
import sympy.Basic


/--
[Algebra_etale_of_moduleFinite_of_flat_of_forall_isUnramifiedAt](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_etale_of_moduleFinite_of_flat_of_forall_isUnramifiedAt.lean)
-/
@[main]
private lemma main
  [CommRing O] [IsNoetherianRing O] [CommRing C] [Algebra O C] [Module.Finite O C] [Module.Flat O C]
-- given
  (h : ∀ (Q : Ideal C) [Q.IsPrime], Algebra.IsUnramifiedAt O Q) :
-- imply
  Algebra.Etale O C := by
-- proof
  haveI : Algebra.FinitePresentation O C := (Algebra.FinitePresentation.of_finiteType).mp inferInstance
  haveI : Algebra.FormallyUnramified O C :=
    Algebra.formallyUnramified_iff_forall.mpr fun q => h q.asIdeal
  exact Algebra.Etale.of_formallyUnramified_of_flat


-- created on 2026-10-01
