import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.PowerSeries.LagrangeBurmannCoefficient
open PowerSeries Finset


/--
[fps_lagrange_burmann_coeff'](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PowerSeries/LagrangeBurmannCoefficient.lean)
-/
@[path]
private lemma fps_lagrange_burmann_coeff'_eq
  [CommRing R]
  {A phi g : PowerSeries R}
  {n : ℕ}
-- given
  (hfix : A = PowerSeries.X * PowerSeries.subst A phi)
  (hn : 0 < n) :
-- imply
  (n : R) * PowerSeries.coeff n (PowerSeries.subst A g) =
    PowerSeries.coeff (n - 1) (PowerSeries.derivative g * phi ^ n) := by
-- proof
  apply fps_lagrange_burmann_coeff' A phi g hfix n hn

/--
[fps_lagrange_burmann_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PowerSeries/LagrangeBurmannCoefficient.lean)
-/
@[path]
private lemma fps_lagrange_burmann_coeff_eq
  [CommRing R]
  {A phi g : PowerSeries R}
  {n : ℕ}
-- given
  (hsubst : PowerSeries.HasSubst A)
  (hphi : PowerSeries.coeff 0 phi ≠ 0)
  (hfix : A = PowerSeries.X * PowerSeries.subst A phi)
  (hn : 0 < n) :
-- imply
  (n : R) * PowerSeries.coeff n (PowerSeries.subst A g) =
    PowerSeries.coeff (n - 1) (PowerSeries.derivative g * phi ^ n) := by
-- proof
  apply fps_lagrange_burmann_coeff A phi g hsubst hphi hfix n hn


-- created on 2026-10-20
