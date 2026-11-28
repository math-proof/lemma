import Def.Data.Vector.Functions
import Def.LinearAlgebra.Matrix.HStack
import Def.LinearAlgebra.Matrix.Rotary
import Def.LinearAlgebra.Matrix.VStack
import Instance.Data.Fin.Fun
import Instance.LinearAlgebra.Matrix.SMul
import Lemma.Fin.CastAdd.ne.NatAdd
import Lemma.Fin.InjectiveNatAdd
open Fin Matrix


private lemma sum_trig
  [AddCommMonoid α]
  {d : ℕ}
  {u v : Fin d → Fin (d + d)}
-- given
  (hu : u.Injective)
  (hv : v.Injective)
  (c : β → α)
  (φ : Fin d → β)
  (a b : Fin d) :
-- imply
  (∑ t : Fin d, if u[a] = u[t] ∧ v[b] = v[t] then c φ[t] else 0) =
    if a = b then c φ[a] else 0 := by
-- proof
  if hab : a = b then
    subst hab
    rw [Finset.sum_eq_single a]
    ·
      simp
    ·
      intro t _ ht
      simp [(hu.ne_iff).mpr ht.symm]
    ·
      intro h
      exact (h (Finset.mem_univ a)).elim
  else
    rw [ite_eq_right hab]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [ite_eq_right]
    intro h
    exact hab ((hu h.1).trans (hv h.2).symm)

private lemma block_uu
  {d : ℕ}
-- given
  (θ : Fin d → ℝ)
  (a b : Fin d) :
-- imply
  Matrix.rotaryOn (Fin.castAdd d) (Fin.natAdd d) θ (a.castAdd d) (b.castAdd d) =
    if a = b then θ.cos[a] else 0 := by
-- proof
  unfold Matrix.rotaryOn
  rw [of_apply, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [_root_.getElem_fin θ, _root_.getElem_fin (Fin.castAdd d), _root_.getElem_fin (Fin.natAdd d)]
  rw [sum_trig (Fin.castAdd_injective d d) (Fin.castAdd_injective d d) Real.cos θ a b]
  have hz :
    (∑ t : Fin d, if (Fin.castAdd d)[a] = (Fin.castAdd d)[t] ∧ (Fin.castAdd d)[b] = (Fin.natAdd d)[t] then -(θ[t].sin) else 0) =
      0 := by
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [ite_eq_right]
    intro hc
    exact CastAdd.ne.NatAdd b t hc.2
  rw [hz]
  have hz :
    (∑ t : Fin d, if (Fin.castAdd d)[a] = (Fin.natAdd d)[t] ∧ (Fin.castAdd d)[b] = (Fin.castAdd d)[t] then θ[t].sin else 0) =
      0 := by
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [ite_eq_right]
    intro hc
    exact CastAdd.ne.NatAdd a t hc.1
  rw [hz]
  have hz :
    (∑ t : Fin d, if (Fin.castAdd d)[a] = (Fin.natAdd d)[t] ∧ (Fin.castAdd d)[b] = (Fin.natAdd d)[t] then θ[t].cos else 0) =
      0 := by
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [ite_eq_right]
    intro hc
    exact CastAdd.ne.NatAdd a t hc.1
  rw [hz]
  simp [Function.cos, Cos.cos]

private lemma block_uv
  {d : ℕ}
-- given
  (θ : Fin d → ℝ)
  (a b : Fin d) :
-- imply
  Matrix.rotaryOn (Fin.castAdd d) (Fin.natAdd d) θ (a.castAdd d) (b.natAdd d) =
    if a = b then -θ.sin[a] else 0 := by
-- proof
  unfold Matrix.rotaryOn
  rw [of_apply, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [_root_.getElem_fin θ, _root_.getElem_fin (Fin.castAdd d), _root_.getElem_fin (Fin.natAdd d)]
  have hz :
    (∑ t : Fin d, if (Fin.castAdd d)[a] = (Fin.castAdd d)[t] ∧ (Fin.natAdd d)[b] = (Fin.castAdd d)[t] then θ[t].cos else 0) =
      0 := by
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [ite_eq_right]
    intro hc
    exact (CastAdd.ne.NatAdd t b).symm hc.2
  rw [hz]
  rw [sum_trig (Fin.castAdd_injective d d) (InjectiveNatAdd d) (fun x => -Real.sin x) θ a b]
  have hz :
    (∑ t : Fin d, if (Fin.castAdd d)[a] = (Fin.natAdd d)[t] ∧ (Fin.natAdd d)[b] = (Fin.castAdd d)[t] then θ[t].sin else 0) =
      0 := by
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [ite_eq_right]
    intro hc
    exact CastAdd.ne.NatAdd a t hc.1
  rw [hz]
  have hz :
    (∑ t : Fin d, if (Fin.castAdd d)[a] = (Fin.natAdd d)[t] ∧ (Fin.natAdd d)[b] = (Fin.natAdd d)[t] then θ[t].cos else 0) =
      0 := by
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [ite_eq_right]
    intro hc
    exact CastAdd.ne.NatAdd a t hc.1
  rw [hz]
  simp [Function.sin, Sin.sin]

private lemma block_vu
  {d : ℕ}
-- given
  (θ : Fin d → ℝ)
  (a b : Fin d) :
-- imply
  Matrix.rotaryOn (Fin.castAdd d) (Fin.natAdd d) θ (a.natAdd d) (b.castAdd d) =
    if a = b then θ.sin[a] else 0 := by
-- proof
  unfold Matrix.rotaryOn
  rw [of_apply, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [_root_.getElem_fin θ, _root_.getElem_fin (Fin.castAdd d), _root_.getElem_fin (Fin.natAdd d)]
  have hz :
    (∑ t : Fin d, if (Fin.natAdd d)[a] = (Fin.castAdd d)[t] ∧ (Fin.castAdd d)[b] = (Fin.castAdd d)[t] then θ[t].cos else 0) =
      0 := by
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [ite_eq_right]
    intro hc
    exact (CastAdd.ne.NatAdd t a).symm hc.1
  rw [hz]
  have hz :
    (∑ t : Fin d, if (Fin.natAdd d)[a] = (Fin.castAdd d)[t] ∧ (Fin.castAdd d)[b] = (Fin.natAdd d)[t] then -(θ[t].sin) else 0) =
      0 := by
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [ite_eq_right]
    intro hc
    exact (CastAdd.ne.NatAdd t a).symm hc.1
  rw [hz]
  rw [sum_trig (InjectiveNatAdd d) (Fin.castAdd_injective d d) Real.sin θ a b]
  have hz :
    (∑ t : Fin d, if (Fin.natAdd d)[a] = (Fin.natAdd d)[t] ∧ (Fin.castAdd d)[b] = (Fin.natAdd d)[t] then θ[t].cos else 0) =
      0 := by
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [ite_eq_right]
    intro hc
    exact CastAdd.ne.NatAdd b t hc.2
  rw [hz]
  simp [Function.sin, Sin.sin]

private lemma block_vv
  {d : ℕ}
-- given
  (θ : Fin d → ℝ)
  (a b : Fin d) :
-- imply
  Matrix.rotaryOn (Fin.castAdd d) (Fin.natAdd d) θ (a.natAdd d) (b.natAdd d) =
    if a = b then θ.cos[a] else 0 := by
-- proof
  unfold Matrix.rotaryOn
  rw [of_apply, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [_root_.getElem_fin θ, _root_.getElem_fin (Fin.castAdd d), _root_.getElem_fin (Fin.natAdd d)]
  have hz :
    (∑ t : Fin d, if (Fin.natAdd d)[a] = (Fin.castAdd d)[t] ∧ (Fin.natAdd d)[b] = (Fin.castAdd d)[t] then θ[t].cos else 0) =
      0 := by
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [ite_eq_right]
    intro hc
    exact (CastAdd.ne.NatAdd t a).symm hc.1
  rw [hz]
  have hz :
    (∑ t : Fin d, if (Fin.natAdd d)[a] = (Fin.castAdd d)[t] ∧ (Fin.natAdd d)[b] = (Fin.natAdd d)[t] then -(θ[t].sin) else 0) =
      0 := by
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [ite_eq_right]
    intro hc
    exact (CastAdd.ne.NatAdd t a).symm hc.1
  rw [hz]
  have hz :
    (∑ t : Fin d, if (Fin.natAdd d)[a] = (Fin.natAdd d)[t] ∧ (Fin.natAdd d)[b] = (Fin.castAdd d)[t] then θ[t].sin else 0) =
      0 := by
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [ite_eq_right]
    intro hc
    exact (CastAdd.ne.NatAdd t b).symm hc.2
  rw [hz]
  rw [sum_trig (InjectiveNatAdd d) (InjectiveNatAdd d) Real.cos θ a b]
  simp [Function.cos, Cos.cos]

@[path]
private lemma main
  {d : ℕ}
-- given
  (θ : Fin d → ℝ) :
-- imply
  Matrix.rotary θ =
    vstack (hstack (θ.cos • 1) (-θ.sin • 1)) (hstack (θ.sin • 1) (θ.cos • 1)) := by
-- proof
  ext i j
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i
  ·
    refine Fin.addCases (fun b => ?_) (fun b => ?_) j
    ·
      simp only [Matrix.rotary]
      rw [block_uu θ a b]
      simp [Matrix.vstack, Matrix.hstack, Matrix.of_apply, vec_smul_apply, one_apply, Fin.val_inj]
    ·
      simp only [Matrix.rotary]
      rw [block_uv θ a b]
      simp [Matrix.vstack, Matrix.hstack, Matrix.of_apply, vec_smul_apply, one_apply, Fin.val_inj]
  ·
    refine Fin.addCases (fun b => ?_) (fun b => ?_) j
    ·
      simp only [Matrix.rotary]
      rw [block_vu θ a b]
      simp [Matrix.vstack, Matrix.hstack, Matrix.of_apply, vec_smul_apply, one_apply, Fin.val_inj]
    ·
      simp only [Matrix.rotary]
      rw [block_vv θ a b]
      simp [Matrix.vstack, Matrix.hstack, Matrix.of_apply, vec_smul_apply, one_apply, Fin.val_inj]


-- created on 2026-11-28
