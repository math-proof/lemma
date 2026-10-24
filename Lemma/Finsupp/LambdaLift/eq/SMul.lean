import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.HeckeAlgebra.OperatorCommutativity
open HeckeAlgebra
open scoped Classical


namespace HeckeAlgebra

/--
[lambdaLift_single](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/OperatorCommutativity.lean)
-/
@[path]
lemma lambdaLift_single
  [DecidableEq B]
  [Fintype B]
  {cs : CoxeterSystem M M.Group}
  {a b : B → R}
  {s : B}
  {w : M.Group}
  {r : R} :
-- imply
  lambdaLift cs a b s (Finsupp.single w r) = r • lambdaOnBasis cs a b s w := by
-- proof
  simp [lambdaLift, Finsupp.linearCombination_single]

end HeckeAlgebra

namespace HeckeAlgebra

/--
[rhoLift_single](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/OperatorCommutativity.lean)
-/
@[path]
lemma rhoLift_single
  [DecidableEq B]
  [Fintype B]
  {cs : CoxeterSystem M M.Group}
  {a b : B → R}
  {t : B}
  {w : M.Group}
  {r : R} :
-- imply
  rhoLift cs a b t (Finsupp.single w r) = r • rhoOnBasis cs a b t w := by
-- proof
  simp [rhoLift, Finsupp.linearCombination_single]

end HeckeAlgebra

namespace HeckeAlgebra

/--
[swt_eq_w_of_length](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/OperatorCommutativity.lean)
-/
@[path]
lemma swt_eq_w_of_length
  [DecidableEq B]
  [Fintype B]
  {cs : CoxeterSystem M M.Group}
  {s t : B}
  {w : M.Group}
-- given
  (h_swt : cs.length (cs.simple s * w * cs.simple t) = cs.length w)
  (h_sw_wt : cs.length (cs.simple s * w) = cs.length (w * cs.simple t)) :
-- imply
  cs.simple s * w * cs.simple t = w := by
-- proof
  have hex := CoxeterExchange.corollary_unconditional cs
  obtain hsw_up | hsw_down := cs.length_simple_mul w s
  · have hwt_up : cs.length (w * cs.simple t) = cs.length w + 1 := by omega
    obtain h_len | h_eq := hex w s t hsw_up hwt_up
    · omega
    · exact h_eq
  · have hs_sw_len : cs.length (cs.simple s * (cs.simple s * w)) =
    cs.length (cs.simple s * w) + 1 := by
    rw [cs.simple_mul_simple_cancel_left s]; omega
    have hswt_len : cs.length (cs.simple s * w * cs.simple t) =
      cs.length (cs.simple s * w) + 1 := by omega
    obtain h_len | h_eq := hex (cs.simple s * w) s t hs_sw_len hswt_len
    · rw [cs.simple_mul_simple_cancel_left s] at h_len; omega
    · rw [cs.simple_mul_simple_cancel_left s] at h_eq
      calc cs.simple s * w * cs.simple t
        = cs.simple s * (w * cs.simple t) := mul_assoc _ _ _
        _ = cs.simple s * (cs.simple s * w) := by rw [h_eq]
        _ = w := cs.simple_mul_simple_cancel_left s

end HeckeAlgebra

namespace HeckeAlgebra

/--
[sw_eq_wt_of_swt_eq_w](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/OperatorCommutativity.lean)
-/
@[path]
lemma sw_eq_wt_of_swt_eq_w
  [DecidableEq B]
  [Fintype B]
  {cs : CoxeterSystem M M.Group}
  {s t : B}
  {w : M.Group}
-- given
  (h : cs.simple s * w * cs.simple t = w) :
-- imply
  cs.simple s * w = w * cs.simple t := by
-- proof
  have h1 : cs.simple s * w * cs.simple t * cs.simple t = w * cs.simple t :=
    congr_arg (· * cs.simple t) h
  rwa [cs.simple_mul_simple_cancel_right] at h1

end HeckeAlgebra

namespace HeckeAlgebra

/--
[lambda_rho_commute_on_basis](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/OperatorCommutativity.lean)
-/
@[path]
lemma lambda_rho_commute_on_basis
  [DecidableEq B]
  [Fintype B]
  {cs : CoxeterSystem M M.Group}
  {sc : StructureConstants B R}
  {s t : B}
  {w : M.Group}
-- given
  (hconj : sc.ConjugacyInvariant cs) :
-- imply
  lambdaLift cs sc.a sc.b s (rhoOnBasis cs sc.a sc.b t w) = rhoLift cs sc.a sc.b t (lambdaOnBasis cs sc.a sc.b s w) := by
-- proof
  have hassoc : cs.simple s * (w * cs.simple t) = cs.simple s * w * cs.simple t :=
    (mul_assoc _ _ _).symm
  have hassoc_len : cs.length (cs.simple s * (w * cs.simple t)) =
    cs.length (cs.simple s * w * cs.simple t) := congrArg cs.length hassoc
  obtain hsw | hsw <;> := cs.length_simple_mul w s
  obtain hwt | hwt := cs.length_mul_simple w t
  ·
    have h4 : cs.length (w * cs.simple t) > cs.length w := by omega
    have h3 : cs.length (cs.simple s * w) > cs.length w := by omega
    obtain hswt_up | hswt_down := cs.length_mul_simple (cs.simple s * w) t
    ·
      have h1 : cs.length (cs.simple s * (w * cs.simple t)) >
        cs.length (w * cs.simple t) := by rw [hassoc_len]; omega
      have h2 : cs.length (cs.simple s * w * cs.simple t) >
        cs.length (cs.simple s * w) := by omega
      simp only [rhoOnBasis, if_pos h4, lambdaLift,
        Finsupp.linearCombination_single, one_smul,
        lambdaOnBasis, if_pos h1, if_pos h3,
        rhoLift, if_pos h2]
      rw [hassoc]
    ·
      have h_len_swt : cs.length (cs.simple s * w * cs.simple t) = cs.length w := by omega
      have h_len_sw_wt : cs.length (cs.simple s * w) = cs.length (w * cs.simple t) := by omega
      have hswt_w := swt_eq_w_of_length cs s t w h_len_swt h_len_sw_wt
      have hsw_wt := sw_eq_wt_of_swt_eq_w cs s t w hswt_w
      have conj : w * cs.simple t * w⁻¹ = cs.simple s := by
        calc w * cs.simple t * w⁻¹
          = cs.simple s * w * w⁻¹ := by rw [← hsw_wt]
          _ = cs.simple s := by group
      have hst := hconj t s w conj
      have h1n : ¬(cs.length (cs.simple s * (w * cs.simple t)) >
        cs.length (w * cs.simple t)) := by rw [hassoc_len]; omega
      have h2n : ¬(cs.length (cs.simple s * w * cs.simple t) >
        cs.length (cs.simple s * w)) := by omega
      simp only [rhoOnBasis, if_pos h4, lambdaLift,
        Finsupp.linearCombination_single, one_smul,
        lambdaOnBasis, if_neg h1n, if_pos h3,
        rhoLift, if_neg h2n]
      rw [hassoc, hswt_w, ← hsw_wt, hst.1, hst.2]
  ·
    have h3 : cs.length (cs.simple s * w) > cs.length w := by omega
    have h4n : ¬(cs.length (w * cs.simple t) > cs.length w) := by omega
    obtain hswt_up | hswt_down := cs.length_mul_simple (cs.simple s * w) t
    ·
      exfalso
      obtain h1 | h1 := cs.length_simple_mul (w * cs.simple t) s
      · rw [hassoc_len] at h1; omega
      · rw [hassoc_len] at h1; omega
    ·
      have h1 : cs.length (cs.simple s * (w * cs.simple t)) >
        cs.length (w * cs.simple t) := by rw [hassoc_len]; omega
      have h2n : ¬(cs.length (cs.simple s * w * cs.simple t) >
        cs.length (cs.simple s * w)) := by omega
      rw [show rhoOnBasis cs sc.a sc.b t w =
        Finsupp.single w (sc.a t) + Finsupp.single (w * cs.simple t) (sc.b t)
        from by simp only [rhoOnBasis, if_neg h4n]]
      rw [show lambdaLift cs sc.a sc.b s
        (Finsupp.single w (sc.a t) + Finsupp.single (w * cs.simple t) (sc.b t)) =
        lambdaLift cs sc.a sc.b s (Finsupp.single w (sc.a t)) +
        lambdaLift cs sc.a sc.b s (Finsupp.single (w * cs.simple t) (sc.b t))
        from map_add _ _ _]
      rw [lambdaLift_single, lambdaLift_single]
      rw [show lambdaOnBasis cs sc.a sc.b s w = Finsupp.single (cs.simple s * w) 1
        from by simp only [lambdaOnBasis, if_pos h3]]
      rw [show lambdaOnBasis cs sc.a sc.b s (w * cs.simple t) =
        Finsupp.single (cs.simple s * (w * cs.simple t)) 1
        from by simp only [lambdaOnBasis, if_pos h1]]
      rw [rhoLift_single, one_smul]
      rw [show rhoOnBasis cs sc.a sc.b t (cs.simple s * w) =
        Finsupp.single (cs.simple s * w) (sc.a t) +
        Finsupp.single (cs.simple s * w * cs.simple t) (sc.b t)
        from by simp only [rhoOnBasis, if_neg h2n]]
      simp only [Finsupp.smul_single', mul_one]
      rw [hassoc]
  ·
    have h3n : ¬(cs.length (cs.simple s * w) > cs.length w) := by omega
    have h4 : cs.length (w * cs.simple t) > cs.length w := by omega
    obtain hswt_up | hswt_down := cs.length_simple_mul (w * cs.simple t) s
    ·
      exfalso
      have hswt_up' : cs.length (cs.simple s * w * cs.simple t) =
        cs.length (w * cs.simple t) + 1 := by rw [← hassoc_len]; exact hswt_up
      obtain h1 | h1 := cs.length_mul_simple (cs.simple s * w) t
      ·
        omega
      ·
        omega
    ·
      have h1n : ¬(cs.length (cs.simple s * (w * cs.simple t)) >
        cs.length (w * cs.simple t)) := by rw [hassoc_len]; omega
      have h2 : cs.length (cs.simple s * w * cs.simple t) >
        cs.length (cs.simple s * w) := by omega
      rw [show rhoOnBasis cs sc.a sc.b t w = Finsupp.single (w * cs.simple t) 1
        from by simp only [rhoOnBasis, if_pos h4]]
      rw [lambdaLift_single, one_smul]
      rw [show lambdaOnBasis cs sc.a sc.b s (w * cs.simple t) =
        Finsupp.single (w * cs.simple t) (sc.a s) +
        Finsupp.single (cs.simple s * (w * cs.simple t)) (sc.b s)
        from by simp only [lambdaOnBasis, if_neg h1n]]
      rw [show lambdaOnBasis cs sc.a sc.b s w =
        Finsupp.single w (sc.a s) + Finsupp.single (cs.simple s * w) (sc.b s)
        from by simp only [lambdaOnBasis, if_neg h3n]]
      rw [show rhoLift cs sc.a sc.b t
        (Finsupp.single w (sc.a s) + Finsupp.single (cs.simple s * w) (sc.b s)) =
        rhoLift cs sc.a sc.b t (Finsupp.single w (sc.a s)) +
        rhoLift cs sc.a sc.b t (Finsupp.single (cs.simple s * w) (sc.b s))
        from map_add _ _ _]
      rw [rhoLift_single, rhoLift_single]
      rw [show rhoOnBasis cs sc.a sc.b t w = Finsupp.single (w * cs.simple t) 1
        from by simp only [rhoOnBasis, if_pos h4]]
      rw [show rhoOnBasis cs sc.a sc.b t (cs.simple s * w) =
        Finsupp.single (cs.simple s * w * cs.simple t) 1
        from by simp only [rhoOnBasis, if_pos h2]]
      simp only [Finsupp.smul_single', mul_one]
      rw [hassoc]
  ·
    have h3n : ¬(cs.length (cs.simple s * w) > cs.length w) := by omega
    have h4n : ¬(cs.length (w * cs.simple t) > cs.length w) := by omega
    obtain hswt_up | hswt_down := cs.length_mul_simple (cs.simple s * w) t
    ·
      have h_len_swt : cs.length (cs.simple s * w * cs.simple t) = cs.length w := by omega
      have h_len_sw_wt : cs.length (cs.simple s * w) = cs.length (w * cs.simple t) := by omega
      have hswt_w := swt_eq_w_of_length cs s t w h_len_swt h_len_sw_wt
      have hsw_wt := sw_eq_wt_of_swt_eq_w cs s t w hswt_w
      have conj : w * cs.simple t * w⁻¹ = cs.simple s := by
        calc w * cs.simple t * w⁻¹
          = cs.simple s * w * w⁻¹ := by rw [← hsw_wt]
          _ = cs.simple s := by group
      have hst := hconj t s w conj
      have h1 : cs.length (cs.simple s * (w * cs.simple t)) >
        cs.length (w * cs.simple t) := by rw [hassoc_len]; omega
      have h2 : cs.length (cs.simple s * w * cs.simple t) >
        cs.length (cs.simple s * w) := by omega
      rw [show rhoOnBasis cs sc.a sc.b t w =
        Finsupp.single w (sc.a t) + Finsupp.single (w * cs.simple t) (sc.b t)
        from by simp only [rhoOnBasis, if_neg h4n]]
      rw [show lambdaLift cs sc.a sc.b s
        (Finsupp.single w (sc.a t) + Finsupp.single (w * cs.simple t) (sc.b t)) =
        lambdaLift cs sc.a sc.b s (Finsupp.single w (sc.a t)) +
        lambdaLift cs sc.a sc.b s (Finsupp.single (w * cs.simple t) (sc.b t))
        from map_add _ _ _]
      rw [lambdaLift_single, lambdaLift_single]
      rw [show lambdaOnBasis cs sc.a sc.b s w =
        Finsupp.single w (sc.a s) + Finsupp.single (cs.simple s * w) (sc.b s)
        from by simp only [lambdaOnBasis, if_neg h3n]]
      rw [show lambdaOnBasis cs sc.a sc.b s (w * cs.simple t) =
        Finsupp.single (cs.simple s * (w * cs.simple t)) 1
        from by simp only [lambdaOnBasis, if_pos h1]]
      rw [show rhoLift cs sc.a sc.b t
        (Finsupp.single w (sc.a s) + Finsupp.single (cs.simple s * w) (sc.b s)) =
        rhoLift cs sc.a sc.b t (Finsupp.single w (sc.a s)) +
        rhoLift cs sc.a sc.b t (Finsupp.single (cs.simple s * w) (sc.b s))
        from map_add _ _ _]
      rw [rhoLift_single, rhoLift_single]
      rw [show rhoOnBasis cs sc.a sc.b t w =
        Finsupp.single w (sc.a t) + Finsupp.single (w * cs.simple t) (sc.b t)
        from by simp only [rhoOnBasis, if_neg h4n]]
      rw [show rhoOnBasis cs sc.a sc.b t (cs.simple s * w) =
        Finsupp.single (cs.simple s * w * cs.simple t) 1
        from by simp only [rhoOnBasis, if_pos h2]]
      rw [hassoc, hswt_w, ← hsw_wt, hst.1, hst.2]
    ·
      have h1n : ¬(cs.length (cs.simple s * (w * cs.simple t)) >
        cs.length (w * cs.simple t)) := by rw [hassoc_len]; omega
      have h2n : ¬(cs.length (cs.simple s * w * cs.simple t) >
        cs.length (cs.simple s * w)) := by omega
      rw [show rhoOnBasis cs sc.a sc.b t w =
        Finsupp.single w (sc.a t) + Finsupp.single (w * cs.simple t) (sc.b t)
        from by simp only [rhoOnBasis, if_neg h4n]]
      rw [show lambdaLift cs sc.a sc.b s
        (Finsupp.single w (sc.a t) + Finsupp.single (w * cs.simple t) (sc.b t)) =
        lambdaLift cs sc.a sc.b s (Finsupp.single w (sc.a t)) +
        lambdaLift cs sc.a sc.b s (Finsupp.single (w * cs.simple t) (sc.b t))
        from map_add _ _ _]
      rw [lambdaLift_single, lambdaLift_single]
      rw [show lambdaOnBasis cs sc.a sc.b s w =
        Finsupp.single w (sc.a s) + Finsupp.single (cs.simple s * w) (sc.b s)
        from by simp only [lambdaOnBasis, if_neg h3n]]
      rw [show lambdaOnBasis cs sc.a sc.b s (w * cs.simple t) =
        Finsupp.single (w * cs.simple t) (sc.a s) +
        Finsupp.single (cs.simple s * (w * cs.simple t)) (sc.b s)
        from by simp only [lambdaOnBasis, if_neg h1n]]
      rw [show rhoLift cs sc.a sc.b t
        (Finsupp.single w (sc.a s) + Finsupp.single (cs.simple s * w) (sc.b s)) =
        rhoLift cs sc.a sc.b t (Finsupp.single w (sc.a s)) +
        rhoLift cs sc.a sc.b t (Finsupp.single (cs.simple s * w) (sc.b s))
        from map_add _ _ _]
      rw [rhoLift_single, rhoLift_single]
      rw [show rhoOnBasis cs sc.a sc.b t w =
        Finsupp.single w (sc.a t) + Finsupp.single (w * cs.simple t) (sc.b t)
        from by simp only [rhoOnBasis, if_neg h4n]]
      rw [show rhoOnBasis cs sc.a sc.b t (cs.simple s * w) =
        Finsupp.single (cs.simple s * w) (sc.a t) +
        Finsupp.single (cs.simple s * w * cs.simple t) (sc.b t)
        from by simp only [rhoOnBasis, if_neg h2n]]
      rw [hassoc]
      simp only [Finsupp.smul_single', smul_add]
      ring_nf
      abel

end HeckeAlgebra

namespace HeckeAlgebra

/--
[isReduced_cons_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/OperatorCommutativity.lean)
-/
@[path]
lemma isReduced_cons_iff
  [DecidableEq B]
  [Fintype B]
  {M' : CoxeterMatrix B'}
  [CommRing R']
  {s : B'}
  {rest : List B'} :
-- imply
  M'.toCoxeterSystem.IsReduced (s :: rest) ↔ M'.toCoxeterSystem.IsReduced rest ∧ M'.toCoxeterSystem.length (M'.toCoxeterSystem.simple s * M'.toCoxeterSystem.wordProd rest) = M'.toCoxeterSystem.length (M'.toCoxeterSystem.wordProd rest) + 1 := by
-- proof
  unfold CoxeterSystem.IsReduced
  simp only [M'.toCoxeterSystem.wordProd_cons, List.length_cons]
  constructor
  · intro h
    have hle := M'.toCoxeterSystem.length_wordProd_le rest
    obtain h1 | h1 := M'.toCoxeterSystem.length_simple_mul (M'.toCoxeterSystem.wordProd rest) s
    · exact ⟨by omega, h1⟩
    · exact ⟨by omega, by omega⟩
  · intro ⟨_, hup⟩; omega

end HeckeAlgebra

namespace HeckeAlgebra

/--
[GenericAlgebra.foldl_gen_left'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/OperatorCommutativity.lean)
-/
@[path]
lemma GenericAlgebra.foldl_gen_left'
  [DecidableEq B]
  [Fintype B]
  {M' : CoxeterMatrix B'}
  [CommRing R']
  {A : GenericAlgebra M' R'}
  {s : B'}
  {init : A.carrier}
  {rest : List B'} :
-- imply
  A.mul (A.basis (M'.toCoxeterSystem.simple s)) (List.foldl (fun acc u => A.mul acc (A.basis (M'.toCoxeterSystem.simple u))) init rest) = List.foldl (fun acc u => A.mul acc (A.basis (M'.toCoxeterSystem.simple u))) (A.mul (A.basis (M'.toCoxeterSystem.simple s)) init) rest := by
-- proof
  induction rest generalizing init with
  | nil => simp
  | cons u rest' ih =>
    simp only [List.foldl_cons]
    rw [ih (A.mul init (A.basis (M'.toCoxeterSystem.simple u)))]
    congr 1
    exact A.gen_left_assoc s init (A.basis (M'.toCoxeterSystem.simple u))

end HeckeAlgebra

namespace HeckeAlgebra

/--
[mul_alt_length_down](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/OperatorCommutativity.lean)
-/
@[path]
lemma mul_alt_length_down
  [DecidableEq B]
  [Fintype B]
  {M' : CoxeterMatrix B'}
  [CommRing R']
  {A : GenericAlgebra M' R'}
  {mul₂ : A.carrier → A.carrier → A.carrier}
-- given
  (h_length_up : ∀ (s : B') (w : M'.Group), M'.toCoxeterSystem.length (M'.toCoxeterSystem.simple s * w) > M'.toCoxeterSystem.length w → mul₂ (A.basis (M'.toCoxeterSystem.simple s)) (A.basis w) = A.basis (M'.toCoxeterSystem.simple s * w))
  (h_quadratic : ∀ (s : B'), mul₂ (A.basis (M'.toCoxeterSystem.simple s)) (A.basis (M'.toCoxeterSystem.simple s)) = A.add (A.smul (A.sc.a s) (A.basis (M'.toCoxeterSystem.simple s))) (A.smul (A.sc.b s) (A.basis 1)))
  (h_identity_left : ∀ x, mul₂ (A.basis 1) x = x)
  (h_mul_add_left : ∀ x y z, mul₂ (A.add x y) z = A.add (mul₂ x z) (mul₂ y z))
  (h_smul_mul_left : ∀ (r : R') x y, mul₂ (A.smul r x) y = A.smul r (mul₂ x y))
  (h_gen_left_assoc : ∀ (s : B') (x y : A.carrier), mul₂ (A.basis (M'.toCoxeterSystem.simple s)) (mul₂ x y) = mul₂ (mul₂ (A.basis (M'.toCoxeterSystem.simple s)) x) y) :
-- imply
  let cs := M'.toCoxeterSystem ∀ (s : B') (w : M'.Group), cs.length (cs.simple s * w) < cs.length w → mul₂ (A.basis (cs.simple s)) (A.basis w) = A.add (A.smul (A.sc.a s) (A.basis w)) (A.smul (A.sc.b s) (A.basis (cs.simple s * w))) := by
-- proof
  intro cs s w hlength
  set sw := cs.simple s * w
  have hw : cs.simple s * sw = w := cs.simple_mul_simple_cancel_left s
  have hlength_up_sw : cs.length (cs.simple s * sw) > cs.length sw := by
    rw [hw]; exact hlength
  have h_Ts_Tsw : mul₂ (A.basis (cs.simple s)) (A.basis sw) = A.basis w := by
    rw [h_length_up s sw hlength_up_sw, hw]
  calc mul₂ (A.basis (cs.simple s)) (A.basis w)
    = mul₂ (A.basis (cs.simple s))
      (mul₂ (A.basis (cs.simple s)) (A.basis sw)) := by
      rw [h_Ts_Tsw]
    _ = mul₂ (mul₂ (A.basis (cs.simple s)) (A.basis (cs.simple s)))
      (A.basis sw) := by
      rw [h_gen_left_assoc]
    _ = mul₂ (A.add (A.smul (A.sc.a s) (A.basis (cs.simple s)))
      (A.smul (A.sc.b s) (A.basis 1)))
      (A.basis sw) := by
      rw [h_quadratic]
    _ = A.add (mul₂ (A.smul (A.sc.a s) (A.basis (cs.simple s))) (A.basis sw))
      (mul₂ (A.smul (A.sc.b s) (A.basis 1)) (A.basis sw)) := by
      rw [h_mul_add_left]
    _ = A.add (A.smul (A.sc.a s) (mul₂ (A.basis (cs.simple s)) (A.basis sw)))
      (A.smul (A.sc.b s) (mul₂ (A.basis 1) (A.basis sw))) := by
      rw [h_smul_mul_left, h_smul_mul_left]
    _ = A.add (A.smul (A.sc.a s) (A.basis w))
      (A.smul (A.sc.b s) (A.basis sw)) := by
      rw [h_Ts_Tsw, h_identity_left]

end HeckeAlgebra

namespace HeckeAlgebra

/--
[mul_alt_gen_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/OperatorCommutativity.lean)
-/
@[path]
lemma mul_alt_gen_eq
  [DecidableEq B]
  [Fintype B]
  {M' : CoxeterMatrix B'}
  [CommRing R']
  {A : GenericAlgebra M' R'}
  {mul₂ : A.carrier → A.carrier → A.carrier}
  {s : B'}
-- given
  (h_length_up : ∀ (s : B') (w : M'.Group), M'.toCoxeterSystem.length (M'.toCoxeterSystem.simple s * w) > M'.toCoxeterSystem.length w → mul₂ (A.basis (M'.toCoxeterSystem.simple s)) (A.basis w) = A.basis (M'.toCoxeterSystem.simple s * w))
  (h_quadratic : ∀ (s : B'), mul₂ (A.basis (M'.toCoxeterSystem.simple s)) (A.basis (M'.toCoxeterSystem.simple s)) = A.add (A.smul (A.sc.a s) (A.basis (M'.toCoxeterSystem.simple s))) (A.smul (A.sc.b s) (A.basis 1)))
  (h_identity_left : ∀ x, mul₂ (A.basis 1) x = x)
  (h_mul_add_right : ∀ x y z, mul₂ x (A.add y z) = A.add (mul₂ x y) (mul₂ x z))
  (h_mul_add_left : ∀ x y z, mul₂ (A.add x y) z = A.add (mul₂ x z) (mul₂ y z))
  (h_mul_smul_right : ∀ (r : R') x y, mul₂ x (A.smul r y) = A.smul r (mul₂ x y))
  (h_smul_mul_left : ∀ (r : R') x y, mul₂ (A.smul r x) y = A.smul r (mul₂ x y))
  (h_gen_left_assoc : ∀ (s : B') (x y : A.carrier), mul₂ (A.basis (M'.toCoxeterSystem.simple s)) (mul₂ x y) = mul₂ (mul₂ (A.basis (M'.toCoxeterSystem.simple s)) x) y) :
-- imply
  ∀ y, mul₂ (A.basis (M'.toCoxeterSystem.simple s)) y = A.mul (A.basis (M'.toCoxeterSystem.simple s)) y := by
-- proof
  apply A.basis_span (fun y =>
    mul₂ (A.basis (M'.toCoxeterSystem.simple s)) y =
    A.mul (A.basis (M'.toCoxeterSystem.simple s)) y)
  ·
    intro w
    obtain h_up | h_down := M'.toCoxeterSystem.length_simple_mul w s
    ·
      rw [h_length_up s w (by omega), A.length_up s w (by omega)]
    ·
      rw [mul_alt_length_down A mul₂ h_length_up h_quadratic h_identity_left
        h_mul_add_left h_smul_mul_left h_gen_left_assoc s w (by omega),
        A.SatisfiesLengthDownRule s w (by omega)]
  ·
    intro y₁ y₂ hy₁ hy₂
    rw [h_mul_add_right, hy₁, hy₂, A.mul_add_right]
  ·
    intro r y hy
    rw [h_mul_smul_right, hy, A.mul_smul_right]

end HeckeAlgebra

namespace HeckeAlgebra

/--
[mul_alt_basis_left_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/OperatorCommutativity.lean)
-/
@[path]
lemma mul_alt_basis_left_eq
  [DecidableEq B]
  [Fintype B]
  {M' : CoxeterMatrix B'}
  [CommRing R']
  {A : GenericAlgebra M' R'}
  {mul₂ : A.carrier → A.carrier → A.carrier}
-- given
  (h_length_up : ∀ (s : B') (w : M'.Group), M'.toCoxeterSystem.length (M'.toCoxeterSystem.simple s * w) > M'.toCoxeterSystem.length w → mul₂ (A.basis (M'.toCoxeterSystem.simple s)) (A.basis w) = A.basis (M'.toCoxeterSystem.simple s * w))
  (h_quadratic : ∀ (s : B'), mul₂ (A.basis (M'.toCoxeterSystem.simple s)) (A.basis (M'.toCoxeterSystem.simple s)) = A.add (A.smul (A.sc.a s) (A.basis (M'.toCoxeterSystem.simple s))) (A.smul (A.sc.b s) (A.basis 1)))
  (h_identity_left : ∀ x, mul₂ (A.basis 1) x = x)
  (h_mul_add_right : ∀ x y z, mul₂ x (A.add y z) = A.add (mul₂ x y) (mul₂ x z))
  (h_mul_add_left : ∀ x y z, mul₂ (A.add x y) z = A.add (mul₂ x z) (mul₂ y z))
  (h_mul_smul_right : ∀ (r : R') x y, mul₂ x (A.smul r y) = A.smul r (mul₂ x y))
  (h_smul_mul_left : ∀ (r : R') x y, mul₂ (A.smul r x) y = A.smul r (mul₂ x y))
  (h_gen_left_assoc : ∀ (s : B') (x y : A.carrier), mul₂ (A.basis (M'.toCoxeterSystem.simple s)) (mul₂ x y) = mul₂ (mul₂ (A.basis (M'.toCoxeterSystem.simple s)) x) y) :
-- imply
  ∀ (w : M'.Group) (y : A.carrier), mul₂ (A.basis w) y = A.mul (A.basis w) y := by
-- proof
  set cs := M'.toCoxeterSystem
  suffices ∀ (n : ℕ) (w : M'.Group), cs.length w ≤ n →
    ∀ y, mul₂ (A.basis w) y = A.mul (A.basis w) y by
    intro w y; exact this (cs.length w) w le_rfl y
  intro n
  induction n with
  | zero =>
    intro w hw y
    have hw1 : w = 1 := cs.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
    subst hw1
    rw [h_identity_left, A.identity_left]
  | succ n ih =>
    intro w hw y
    by_cases hw1 : w = 1
    · subst hw1; rw [h_identity_left, A.identity_left]
    · obtain ⟨s, hs⟩ := cs.exists_leftDescent_of_ne_one hw1
      set sw := cs.simple s * w
      have hsw_lt : cs.length sw < cs.length w := hs
      have hs_sw : cs.length (cs.simple s * sw) > cs.length sw := by
        rw [cs.simple_mul_simple_cancel_left s]; exact hsw_lt
      have h_mul2_TsTsw : mul₂ (A.basis (cs.simple s)) (A.basis sw) = A.basis w := by
        rw [h_length_up s sw hs_sw, cs.simple_mul_simple_cancel_left s]
      have h_mul_TsTsw : A.mul (A.basis (cs.simple s)) (A.basis sw) = A.basis w := by
        rw [A.length_up s sw hs_sw, cs.simple_mul_simple_cancel_left s]
      calc mul₂ (A.basis w) y
        = mul₂ (mul₂ (A.basis (cs.simple s)) (A.basis sw)) y := by
          rw [h_mul2_TsTsw]
        _ = mul₂ (A.basis (cs.simple s)) (mul₂ (A.basis sw) y) := by
          rw [← h_gen_left_assoc]
        _ = mul₂ (A.basis (cs.simple s)) (A.mul (A.basis sw) y) := by
          rw [ih sw (by omega) y]
        _ = A.mul (A.basis (cs.simple s)) (A.mul (A.basis sw) y) := by
          rw [mul_alt_gen_eq A mul₂ h_length_up h_quadratic h_identity_left
            h_mul_add_right h_mul_add_left h_mul_smul_right h_smul_mul_left
            h_gen_left_assoc s]
        _ = A.mul (A.mul (A.basis (cs.simple s)) (A.basis sw)) y := by
          rw [A.gen_left_assoc]
        _ = A.mul (A.basis w) y := by
          rw [h_mul_TsTsw]

end HeckeAlgebra

namespace HeckeAlgebra

/--
[generic_algebra_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/OperatorCommutativity.lean)
-/
@[path]
lemma generic_algebra_unique
  [DecidableEq B]
  [Fintype B]
  {M' : CoxeterMatrix B'}
  [CommRing R']
  {A : GenericAlgebra M' R'}
  {mul₂ : A.carrier → A.carrier → A.carrier}
-- given
  (h_length_up : ∀ (s : B') (w : M'.Group), M'.toCoxeterSystem.length (M'.toCoxeterSystem.simple s * w) > M'.toCoxeterSystem.length w → mul₂ (A.basis (M'.toCoxeterSystem.simple s)) (A.basis w) = A.basis (M'.toCoxeterSystem.simple s * w))
  (h_quadratic : ∀ (s : B'), mul₂ (A.basis (M'.toCoxeterSystem.simple s)) (A.basis (M'.toCoxeterSystem.simple s)) = A.add (A.smul (A.sc.a s) (A.basis (M'.toCoxeterSystem.simple s))) (A.smul (A.sc.b s) (A.basis 1)))
  (h_identity_left : ∀ x, mul₂ (A.basis 1) x = x)
  (h_identity_right : ∀ x, mul₂ x (A.basis 1) = x)
  (h_mul_add_right : ∀ x y z, mul₂ x (A.add y z) = A.add (mul₂ x y) (mul₂ x z))
  (h_mul_add_left : ∀ x y z, mul₂ (A.add x y) z = A.add (mul₂ x z) (mul₂ y z))
  (h_mul_smul_right : ∀ (r : R') x y, mul₂ x (A.smul r y) = A.smul r (mul₂ x y))
  (h_smul_mul_left : ∀ (r : R') x y, mul₂ (A.smul r x) y = A.smul r (mul₂ x y))
  (h_gen_left_assoc : ∀ (s : B') (x y : A.carrier), mul₂ (A.basis (M'.toCoxeterSystem.simple s)) (mul₂ x y) = mul₂ (mul₂ (A.basis (M'.toCoxeterSystem.simple s)) x) y)
  (h_gen_right_assoc : ∀ (t : B') (x y : A.carrier), mul₂ (mul₂ x y) (A.basis (M'.toCoxeterSystem.simple t)) = mul₂ x (mul₂ y (A.basis (M'.toCoxeterSystem.simple t)))) :
-- imply
  ∀ x y, mul₂ x y = A.mul x y := by
-- proof
  have h_basis_left : ∀ (w : M'.Group) (y : A.carrier),
    mul₂ (A.basis w) y = A.mul (A.basis w) y :=
    mul_alt_basis_left_eq A mul₂ h_length_up h_quadratic h_identity_left
      h_mul_add_right h_mul_add_left h_mul_smul_right h_smul_mul_left
      h_gen_left_assoc
  intro x
  apply A.basis_span (fun x => ∀ y, mul₂ x y = A.mul x y)
  ·
    exact h_basis_left
  ·
    intro x₁ x₂ hx₁ hx₂ y
    rw [h_mul_add_left, hx₁, hx₂, A.mul_add_left]
  ·
    intro r x hx y
    rw [h_smul_mul_left, hx, A.smul_mul_left]

end HeckeAlgebra


-- created on 2026-10-23
