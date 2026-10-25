import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailCone.Part4
open StatMech StatMech.Exact3D StatMech.Exact3D.FinitePlusTailState StatMech.Exact3D.FinitePlusTailLipschitzCertificate StatMech.Exact3D.FinitePlusTailHyperbolicSplitting StatMech.Exact3D.FinitePlusTailConeCertificate


/--
[mixedNorm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailCone.lean)
-/
@[path]
private lemma mixedNorm_nonneg_eq
  {n : ℕ}
  {x : FinitePlusTailState n α} :
-- imply
  0 ≤ mixedNorm x := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailState.mixedNorm_nonneg x

/--
[mixedNorm_map_le_mul_of_map_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailCone.lean)
-/
@[path]
private lemma mixedNorm_map_le_mul_of_map_origin_eq
  {n : ℕ}
  {C : FinitePlusTailLipschitzCertificate n α}
  {x : FinitePlusTailState n α}
-- given
  (h0 : C.map (FinitePlusTailState.origin : FinitePlusTailState n α) = FinitePlusTailState.origin) :
-- imply
  FinitePlusTailState.mixedNorm (C.map x) ≤ C.c * FinitePlusTailState.mixedNorm x := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailLipschitzCertificate.mixedNorm_map_le_mul_of_map_origin C h0 x

/--
[map_mem_thermalStableCone_of_c_le_abs_thermal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailCone.lean)
-/
@[path]
private lemma map_mem_thermalStableCone_of_c_le_abs_thermal_eq
  {n : ℕ}
  {C : FinitePlusTailLipschitzCertificate n α}
  {thermal η t : ℝ}
  {s : FinitePlusTailState n α}
-- given
  (h0 : C.map (FinitePlusTailState.origin : FinitePlusTailState n α) = FinitePlusTailState.origin)
  (hη : 0 ≤ η)
  (hdom : C.c ≤ |thermal|)
  (hs : FinitePlusTailState.ThermalStableCone η t s) :
-- imply
  FinitePlusTailState.ThermalStableCone η (thermal * t) (C.map s) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailLipschitzCertificate.map_mem_thermalStableCone_of_c_le_abs_thermal C h0 hη hdom hs

/--
[iterate_origin_of_map_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailCone.lean)
-/
@[path]
private lemma iterate_origin_of_map_origin_eq
  {n : ℕ}
  {C : FinitePlusTailLipschitzCertificate n α}
  {k : ℕ}
-- given
  (h0 : C.map (FinitePlusTailState.origin : FinitePlusTailState n α) = FinitePlusTailState.origin) :
-- imply
  C.iterate k (FinitePlusTailState.origin : FinitePlusTailState n α) = FinitePlusTailState.origin := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailLipschitzCertificate.iterate_origin_of_map_origin C h0 k

/--
[iterate_mem_thermalStableCone_of_c_le_abs_thermal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailCone.lean)
-/
@[path]
private lemma iterate_mem_thermalStableCone_of_c_le_abs_thermal_eq
  {n : ℕ}
  {C : FinitePlusTailLipschitzCertificate n α}
  {thermal η t : ℝ}
  {s : FinitePlusTailState n α}
  {k : ℕ}
-- given
  (h0 : C.map (FinitePlusTailState.origin : FinitePlusTailState n α) = FinitePlusTailState.origin)
  (hη : 0 ≤ η)
  (hdom : C.c ≤ |thermal|)
  (hs : FinitePlusTailState.ThermalStableCone η t s) :
-- imply
  FinitePlusTailState.ThermalStableCone η (thermal ^ k * t) (C.iterate k s) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailLipschitzCertificate.iterate_mem_thermalStableCone_of_c_le_abs_thermal C h0 hη hdom hs k

/--
[step_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailCone.lean)
-/
@[path]
private lemma step_origin_eq
  {n : ℕ}
  {H : FinitePlusTailHyperbolicSplitting n α} :
-- imply
  H.step origin = origin := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.step_origin H

/--
[iterate_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailCone.lean)
-/
@[path]
private lemma iterate_origin_eq
  {n : ℕ}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {k : ℕ} :
-- imply
  H.iterate k origin = origin := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.iterate_origin H k

/--
[iterate_fst_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailCone.lean)
-/
@[path]
private lemma iterate_fst_eq_eq
  {n : ℕ}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {k : ℕ}
  {x : State n α} :
-- imply
  (H.iterate k x).1 = H.thermal ^ k * x.1 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.iterate_fst_eq H k x

/--
[iterate_snd_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailCone.lean)
-/
@[path]
private lemma iterate_snd_eq_eq
  {n : ℕ}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {k : ℕ}
  {x : State n α} :
-- imply
  (H.iterate k x).2 = H.stable.iterate k x.2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.iterate_snd_eq H k x

/--
[cone_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailCone.lean)
-/
@[path]
private lemma cone_step_eq
  {n : ℕ}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {η : ℝ}
  {x : State n α}
-- given
  (hη : 0 ≤ η)
  (hx : H.cone η x) :
-- imply
  H.cone η (H.step x) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.cone_step H hη hx

/--
[cone_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailCone.lean)
-/
@[path]
private lemma cone_iterate_eq
  {n : ℕ}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {η : ℝ}
  {x : State n α}
  {k : ℕ}
-- given
  (hη : 0 ≤ η)
  (hx : H.cone η x) :
-- imply
  H.cone η (H.iterate k x) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.cone_iterate H hη hx k

/--
[cone_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailCone.lean)
-/
@[path]
private lemma cone_step_eq_2
  {n : ℕ}
  {C : FinitePlusTailConeCertificate n α}
  {η : ℝ}
  {x : FinitePlusTailState n α}
-- given
  (hη : 0 ≤ η)
  (hx : C.cone η x) :
-- imply
  C.cone η (C.contraction.map x) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailConeCertificate.cone_step C hη hx

/--
[thermal_iterate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailCone.lean)
-/
@[path]
private lemma thermal_iterate_eq_eq
  {n : ℕ}
  {C : FinitePlusTailConeCertificate n α}
  {k : ℕ}
  {x : FinitePlusTailState n α} :
-- imply
  C.thermal (C.contraction.iterate k x) = C.thermalMultiplier ^ k * C.thermal x := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailConeCertificate.thermal_iterate_eq C k x

/--
[stableSize_iterate_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailCone.lean)
-/
@[path]
private lemma stableSize_iterate_le_eq
  {n : ℕ}
  {C : FinitePlusTailConeCertificate n α}
  {k : ℕ}
  {x : FinitePlusTailState n α} :
-- imply
  C.stableSize (C.contraction.iterate k x) ≤ C.stableStepConstant ^ k * C.stableSize x := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailConeCertificate.stableSize_iterate_le C k x

/--
[cone_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailCone.lean)
-/
@[path]
private lemma cone_iterate_eq_2
  {n : ℕ}
  {C : FinitePlusTailConeCertificate n α}
  {η : ℝ}
  {x : FinitePlusTailState n α}
  {k : ℕ}
-- given
  (hη : 0 ≤ η)
  (hx : C.cone η x) :
-- imply
  C.cone η (C.contraction.iterate k x) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailConeCertificate.cone_iterate C hη hx k

/--
[cone_iterate_closed_form](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailCone.lean)
-/
@[path]
private lemma cone_iterate_closed_form_eq
  {n : ℕ}
  {C : FinitePlusTailConeCertificate n α}
  {η : ℝ}
  {x : FinitePlusTailState n α}
  {k : ℕ}
-- given
  (hη : 0 ≤ η)
  (hx : C.cone η x) :
-- imply
  C.stableSize (C.contraction.iterate k x) ≤ η * := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailConeCertificate.cone_iterate_closed_form C hη hx k


-- created on 2026-10-23
