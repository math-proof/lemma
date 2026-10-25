import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc86brerouteinjection.Part4
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc86b_o_connects_mark](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc86brerouteinjection.lean)
-/
@[path]
private lemma gc86b_o_connects_mark_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {R : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i ∈ R, ¬ (ends i).IsDiag)
  (hsrc : sources ends R = ({o, x, y, g} : Finset W))
  (ho : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g) :
-- imply
  connK ends R o x ∨ connK ends R o y ∨ connK ends R o g := by
-- proof
  apply StatMech.Walls.gc86b_o_connects_mark ends R hnd hsrc ho hoy hog

/--
[gc86b_ncount_conn_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc86brerouteinjection.lean)
-/
@[path]
private lemma gc86b_ncount_conn_eq_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {R : Finset ι}
  {u v : W}
-- given
  (huv : u ≠ v)
  (hconn : connK ends R u v) :
-- imply
  gc86b_ncount ends R {u, v} = gc86b_ncount ends R ∅ := by
-- proof
  apply StatMech.Walls.gc86b_ncount_conn_eq ends R huv hconn

/--
[gc86b_strong_of_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc86brerouteinjection.lean)
-/
@[path]
private lemma gc86b_strong_of_conn_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {R : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i ∈ R, ¬ (ends i).IsDiag)
  (hsrc : sources ends R = ({o, x, y, g} : Finset W))
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g) :
-- imply
  gc86b_ncount ends R ∅ ≤ gc86b_ncount ends R {o, x} + gc86b_ncount ends R {o, y} + gc86b_ncount ends R {o, g} := by
-- proof
  apply StatMech.Walls.gc86b_strong_of_conn ends R hnd hsrc hox hoy hog

/--
[gc85b_pcount_fiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc86brerouteinjection.lean)
-/
@[path]
private lemma gc85b_pcount_fiber_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {A B : Finset W} :
-- imply
  gc85b_pcount ends m A B = ∑ K₁ ∈ m.powerset.filter (fun K => sources ends K = A), gc86b_ncount ends (m \ K₁) B := by
-- proof
  apply StatMech.Walls.gc85b_pcount_fiber ends m A B

/--
[gc86b_sources_sdiff_of_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc86brerouteinjection.lean)
-/
@[path]
private lemma gc86b_sources_sdiff_of_empty_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m K₁ : Finset ι}
-- given
  (hK₁m : K₁ ⊆ m)
  (hK₁ : sources ends K₁ = ∅) :
-- imply
  sources ends (m \ K₁) = sources ends m := by
-- proof
  apply StatMech.Walls.gc86b_sources_sdiff_of_empty ends hK₁m hK₁

/--
[gc86b_strong_global](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc86brerouteinjection.lean)
-/
@[path]
private lemma gc86b_strong_global_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hsrc : sources ends m = ({o, x, y, g} : Finset W))
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g) :
-- imply
  gc85b_pcount ends m ∅ ∅ ≤ gc85b_pcount ends m ∅ {o, g} + gc85b_pcount ends m ∅ {o, x} + gc85b_pcount ends m ∅ {o, y} := by
-- proof
  apply StatMech.Walls.gc86b_strong_global ends m hnd hsrc hox hoy hog

/--
[gc86b_bijection_iff_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc86brerouteinjection.lean)
-/
@[path]
private lemma gc86b_bijection_iff_residual_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W} :
-- imply
  gc85b_ThreeCurrentBijection ends m o x y g ↔ gc86b_CogxgResidual ends m o x y g := by
-- proof
  apply StatMech.Walls.gc86b_bijection_iff_residual ends m o x y g

/--
[gc86b_bijection_of_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc86brerouteinjection.lean)
-/
@[path]
private lemma gc86b_bijection_of_residual_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
-- given
  (hres : gc86b_CogxgResidual ends m o x y g) :
-- imply
  gc85b_ThreeCurrentBijection ends m o x y g := by
-- proof
  apply StatMech.Walls.gc86b_bijection_of_residual ends m o x y g hres

/--
[gc86b_star_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc86brerouteinjection.lean)
-/
@[path]
private lemma gc86b_star_sources_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  sources gc86b_starEnds (univ : Finset (Fin 4)) = ({0, 1, 2, 3} : Finset (Fin 5)) := by
-- proof
  apply StatMech.Walls.gc86b_star_sources

/--
[gc86b_star_bijection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc86brerouteinjection.lean)
-/
@[path]
private lemma gc86b_star_bijection_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  gc85b_ThreeCurrentBijection gc86b_starEnds (univ : Finset (Fin 4)) 0 1 2 3 ∧ gc85b_pcount gc86b_starEnds (univ : Finset (Fin 4)) ∅ ∅ = 1 := by
-- proof
  apply StatMech.Walls.gc86b_star_bijection

/--
[gc86b_reroute_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc86brerouteinjection.lean)
-/
@[path]
private lemma gc86b_reroute_status_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hsrc : sources ends m = ({o, x, y, g} : Finset W))
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g) :
-- imply
  (connK ends m o x ∨ connK ends m o y ∨ connK ends m o g) ∧ (gc85b_pcount ends m ∅ ∅ ≤ gc85b_pcount ends m ∅ {o, g} + gc85b_pcount ends m ∅ {o, x} + gc85b_pcount ends m ∅ {o, y}) ∧ (gc86b_CogxgResidual ends m o x y g ↔ gc85b_ThreeCurrentBijection ends m o x y g) := by
-- proof
  apply StatMech.Walls.gc86b_reroute_status ends m hnd hsrc hox hoy hog


-- created on 2026-10-23
