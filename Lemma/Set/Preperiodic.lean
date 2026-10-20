import Mathlib
import sympy.Basic
import sympy.atlas.Dynamics.Preperiodic
open Function


/--
[mem_forwardOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean)
-/
@[path]
private lemma mem_forwardOrbit_eq
  {f : α → α}
  {x y z : α}
  {m n : ℕ} :
-- imply
  y ∈ forwardOrbit f x ↔ ∃ n : ℕ, f^[n] x = y := by
-- proof
  apply Function.mem_forwardOrbit

/--
[mem_forwardOrbit_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean)
-/
@[path]
private lemma mem_forwardOrbit_self_eq
  {x y z : α}
  {f : α → α}
  {x : α} :
-- imply
  x ∈ forwardOrbit f x := by
-- proof
  apply Function.mem_forwardOrbit_self f x

/--
[forwardOrbit_eq_range](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean)
-/
@[path]
private lemma forwardOrbit_eq_range_eq
  {x y z : α}
  {m n : ℕ}
  {f : α → α}
  {x : α} :
-- imply
  forwardOrbit f x = Set.range (fun n : ℕ => f^[n] x) := by
-- proof
  apply Function.forwardOrbit_eq_range f x

/--
[isPreperiodicPt_iff_exists_eq_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean)
-/
@[path]
private lemma isPreperiodicPt_iff_exists_eq_iterate_eq
  {f : α → α}
  {x y z : α}
  {m n : ℕ} :
-- imply
  IsPreperiodicPt f x ↔ ∃ m n : ℕ, m < n ∧ f^[m] x = f^[n] x := by
-- proof
  apply Function.isPreperiodicPt_iff_exists_eq_iterate

/--
[isStrictlyPreperiodicPt_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean)
-/
@[path]
private lemma isStrictlyPreperiodicPt_iff_eq
  {f : α → α}
  {x y z : α} :
-- imply
  IsStrictlyPreperiodicPt f x ↔ IsPreperiodicPt f x ∧ x ∉ periodicPts f := by
-- proof
  apply Function.isStrictlyPreperiodicPt_iff

/--
[isPreperiodicPtOfType_iff_isPeriodicPt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean)
-/
@[path]
private lemma isPreperiodicPtOfType_iff_isPeriodicPt_eq
  {f : α → α}
  {x y z : α}
  {m n : ℕ} :
-- imply
  IsPreperiodicPtOfType f m n x ↔ 0 < n ∧ IsPeriodicPt f n (f^[m] x) := by
-- proof
  apply Function.isPreperiodicPtOfType_iff_isPeriodicPt

/--
[IsPreperiodicPtOfType.isPreperiodicPt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean)
-/
@[path]
private lemma IsPreperiodicPtOfType_isPreperiodicPt_eq
  {f : α → α}
  {x y z : α}
  {m n : ℕ}
-- given
  (h : IsPreperiodicPtOfType f m n x) :
-- imply
  IsPreperiodicPt f x := by
-- proof
  apply Function.IsPreperiodicPtOfType.isPreperiodicPt h

/--
[grandOrbitRel_refl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean)
-/
@[path]
private lemma grandOrbitRel_refl_eq
  {x y z : α}
  {f : α → α}
  {x : α} :
-- imply
  GrandOrbitRel f x x := by
-- proof
  apply Function.grandOrbitRel_refl f x

/--
[GrandOrbitRel.symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean)
-/
@[path]
private lemma GrandOrbitRel_symm_eq
  {f : α → α}
  {x y z : α}
-- given
  (h : GrandOrbitRel f x y) :
-- imply
  GrandOrbitRel f y x := by
-- proof
  apply Function.GrandOrbitRel.symm h

/--
[GrandOrbitRel.trans](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean)
-/
@[path]
private lemma GrandOrbitRel_trans_eq
  {f : α → α}
  {x y z : α}
-- given
  (hxy : GrandOrbitRel f x y)
  (hyz : GrandOrbitRel f y z) :
-- imply
  GrandOrbitRel f x z := by
-- proof
  apply Function.GrandOrbitRel.trans hxy hyz

/--
[grandOrbitRel_equivalence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean)
-/
@[path]
private lemma grandOrbitRel_equivalence_eq
  {f : α → α} :
-- imply
  Equivalence (GrandOrbitRel f) where
    refl := by
-- proof
  apply Function.grandOrbitRel_equivalence f

/--
[mem_grandOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean)
-/
@[path]
private lemma mem_grandOrbit_eq
  {f : α → α}
  {x y z : α} :
-- imply
  y ∈ grandOrbit f x ↔ GrandOrbitRel f x y := by
-- proof
  apply Function.mem_grandOrbit

/--
[grandOrbitRel_iff_inter_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean)
-/
@[path]
private lemma grandOrbitRel_iff_inter_nonempty_eq
  {f : α → α}
  {x y z : α} :
-- imply
  GrandOrbitRel f x y ↔ (forwardOrbit f x ∩ forwardOrbit f y).Nonempty := by
-- proof
  apply Function.grandOrbitRel_iff_inter_nonempty


-- created on 2026-10-20
