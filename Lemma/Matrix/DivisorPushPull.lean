import Class.AlgebraicCurve_DivisorPushPull

/-!
Re-export of Class.AlgebraicCurve_DivisorPushPull.

The push/pull, FundamentalIdentity, and SumRamificationInertia API now lives
in Class so it can be imported without the Class to Lemma to Instance cycle.
This module keeps the old Lemma.Matrix.DivisorPushPull import path
for remaining unowned Lemma importers (Rat, Int, Matrix, ModularCurve).
It declares nothing of its own.
-/
