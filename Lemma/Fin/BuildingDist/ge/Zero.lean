import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.Building.AffineCurvature.Part2
open ChamberComplex AffineBuilding


/--
[buildingDist_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineCurvature.lean)
-/
@[path]
private lemma main
  [DecidableEq V]
  {b : Building V}
  {md : ApartmentMetricData b}
  {x y : V} :
-- imply
  0 ≤ buildingDist b md x y := by
-- proof
  unfold buildingDist
  split
  · exact md.dist_nonneg _ x y
  · exact le_refl 0



/--
[buildingDist_eq_dist_fn](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineCurvature.lean)
-/
private lemma buildingDist_eq_dist_fn
  [DecidableEq V]
  {b : Building V}
  {md : ApartmentMetricData b}
  {u v : V}
-- given
  (A : { A // A ∈ b.apartmentSystem.apartments })
  (huA : ∃ s ∈ A.val.faces, u ∈ s)
  (hvA : ∃ s ∈ A.val.faces, v ∈ s) :
-- imply
  buildingDist b md u v = md.dist_fn A u v := by
-- proof
  unfold buildingDist
  split
  · next h =>
    exact buildingDist_well_defined_general b md h.choose A u v
      h.choose_spec.1 h.choose_spec.2 huA hvA
  · next h =>
    exact absurd ⟨A, huA, hvA⟩ h



/--
[euclidean_identity_ips](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineCurvature.lean)
-/
private lemma euclidean_identity_ips
  [DecidableEq V]
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {x y : E}
  {t : ℝ} :
-- imply
  ‖t • x + (1 - t) • y‖ ^ 2 = t * ‖x‖ ^ 2 + (1 - t) * ‖y‖ ^ 2 - t * (1 - t) * ‖x - y‖ ^ 2 := by
-- proof
  have hx : ‖x‖ ^ 2 = @inner ℝ E _ x x := by rw [real_inner_self_eq_norm_sq]
  have hy : ‖y‖ ^ 2 = @inner ℝ E _ y y := by rw [real_inner_self_eq_norm_sq]
  have hsymm : @inner ℝ E _ y x = @inner ℝ E _ x y := by rw [real_inner_comm]
  have hxy : ‖x - y‖ ^ 2 = @inner ℝ E _ x x - 2 * @inner ℝ E _ x y +
    @inner ℝ E _ y y := by
    rw [norm_sub_sq_real x y, hx, hy]
  have hlhs : ‖t • x + (1 - t) • y‖ ^ 2 =
    @inner ℝ E _ (t • x + (1 - t) • y) (t • x + (1 - t) • y) := by
    rw [real_inner_self_eq_norm_sq]
  rw [hlhs]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real]
  rw [hx, hy, hxy, hsymm]
  ring



/--
[euclidean_identity_origin_shifted](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineCurvature.lean)
-/
private lemma euclidean_identity_origin_shifted
  [DecidableEq V]
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {q x y z_t : E}
  {t : ℝ}
-- given
  (h_zt : z_t = t • x + (1 - t) • y) :
-- imply
  ‖q - z_t‖ ^ 2 = t * ‖q - x‖ ^ 2 + (1 - t) * ‖q - y‖ ^ 2 - t * (1 - t) * ‖x - y‖ ^ 2 := by
-- proof
  have key : q - z_t = -(t • (x - q) + (1 - t) • (y - q)) := by
    rw [h_zt]; simp only [smul_sub, neg_add_rev]; module
  rw [key, norm_neg]
  rw [norm_sub_rev q x, norm_sub_rev q y]
  have hsub : (x - q) - (y - q) = x - y := by abel
  rw [← hsub]
  exact euclidean_identity_ips (x - q) (y - q) t



/--
[euclidean_identity_in_apartment](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineCurvature.lean)
-/
private lemma euclidean_identity_in_apartment
  [DecidableEq V]
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {b : Building V}
  {md : ApartmentMetricData b}
  {x y q z_t : V}
  {t : ℝ}
-- given
  (coord : { A : SimplicialComplex V // A ∈ b.apartmentSystem.apartments } → V → E)
  (dist_eq_norm : ∀ (A : { A // A ∈ b.apartmentSystem.apartments }) (u v : V), md.dist_fn A u v = ‖coord A u - coord A v‖)
  (coord_geodesic : ∀ (A : { A // A ∈ b.apartmentSystem.apartments }) (x y z_t : V) (t : ℝ), (∃ s ∈ A.val.faces, x ∈ s) → (∃ s ∈ A.val.faces, y ∈ s) → (∃ s ∈ A.val.faces, z_t ∈ s) → md.dist_fn A z_t x = (1 - t) * md.dist_fn A x y → md.dist_fn A z_t y = t * md.dist_fn A x y → coord A z_t = t • coord A x + (1 - t) • coord A y)
  (_ht0 : 0 ≤ t)
  (_ht1 : t ≤ 1)
  (hzt_x : buildingDist b md z_t x = (1 - t) * buildingDist b md x y)
  (hzt_y : buildingDist b md z_t y = t * buildingDist b md x y)
  (A : { A // A ∈ b.apartmentSystem.apartments })
  (hqA : ∃ s ∈ A.val.faces, q ∈ s)
  (hxA : ∃ s ∈ A.val.faces, x ∈ s)
  (hyA : ∃ s ∈ A.val.faces, y ∈ s)
  (hztA : ∃ s ∈ A.val.faces, z_t ∈ s) :
-- imply
  (buildingDist b md q z_t) ^ 2 = t * (buildingDist b md q x) ^ 2 + (1 - t) * (buildingDist b md q y) ^ 2 - t * (1 - t) * (buildingDist b md x y) ^ 2 := by
-- proof
  rw [buildingDist_eq_dist_fn b md A q z_t hqA hztA,
    buildingDist_eq_dist_fn b md A q x hqA hxA,
    buildingDist_eq_dist_fn b md A q y hqA hyA,
    buildingDist_eq_dist_fn b md A x y hxA hyA]
  rw [dist_eq_norm A q z_t, dist_eq_norm A q x,
    dist_eq_norm A q y, dist_eq_norm A x y]
  have hzt_x_A : md.dist_fn A z_t x = (1 - t) * md.dist_fn A x y := by
    rw [← buildingDist_eq_dist_fn b md A z_t x hztA hxA,
      ← buildingDist_eq_dist_fn b md A x y hxA hyA]; exact hzt_x
  have hzt_y_A : md.dist_fn A z_t y = t * md.dist_fn A x y := by
    rw [← buildingDist_eq_dist_fn b md A z_t y hztA hyA,
      ← buildingDist_eq_dist_fn b md A x y hxA hyA]; exact hzt_y
  have hcoord := coord_geodesic A x y z_t t hxA hyA hztA hzt_x_A hzt_y_A
  exact euclidean_identity_origin_shifted (coord A q) (coord A x) (coord A y)
    (coord A z_t) t hcoord



/--
[negCurvatureIneq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineCurvature.lean)
-/
private lemma negCurvatureIneq
  [DecidableEq V]
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {b : Building V}
  {md : ApartmentMetricData b}
-- given
  (coord : { A : SimplicialComplex V // A ∈ b.apartmentSystem.apartments } → V → E)
  (dist_eq_norm : ∀ (A : { A // A ∈ b.apartmentSystem.apartments }) (u v : V), md.dist_fn A u v = ‖coord A u - coord A v‖)
  (coord_geodesic : ∀ (A : { A // A ∈ b.apartmentSystem.apartments }) (x y z_t : V) (t : ℝ), (∃ s ∈ A.val.faces, x ∈ s) → (∃ s ∈ A.val.faces, y ∈ s) → (∃ s ∈ A.val.faces, z_t ∈ s) → md.dist_fn A z_t x = (1 - t) * md.dist_fn A x y → md.dist_fn A z_t y = t * md.dist_fn A x y → coord A z_t = t • coord A x + (1 - t) • coord A y)
  (retract_exists : ∀ (x y z z_t : V), ∃ (ρ : V → V) (A : { A // A ∈ b.apartmentSystem.apartments }), (∃ s ∈ A.val.faces, x ∈ s) ∧ (∃ s ∈ A.val.faces, y ∈ s) ∧ (∃ s ∈ A.val.faces, ρ z ∈ s) ∧ ρ x = x ∧ ρ y = y ∧ (∀ u v, buildingDist b md (ρ u) (ρ v) ≤ buildingDist b md u v) ∧ buildingDist b md z z_t = buildingDist b md (ρ z) z_t)
  (zt_in_apt : ∀ (x y z_t : V) (t : ℝ), 0 ≤ t → t ≤ 1 → buildingDist b md z_t x = (1 - t) * buildingDist b md x y → buildingDist b md z_t y = t * buildingDist b md x y → ∀ (A : { A // A ∈ b.apartmentSystem.apartments }), (∃ s ∈ A.val.faces, x ∈ s) → (∃ s ∈ A.val.faces, y ∈ s) → (∃ s ∈ A.val.faces, z_t ∈ s)) :
-- imply
  NegCurvatureIneq b md := by
-- proof
  intro x y z z_t t ht0 ht1 hzt_x hzt_y
  obtain ⟨ρ, A, hxA, hyA, hρzA, hρ_fix_x, hρ_fix_y, hρ_nonincr, hρ_isom⟩ :=
    retract_exists x y z z_t
  have hztA := zt_in_apt x y z_t t ht0 ht1 hzt_x hzt_y A hxA hyA
  have h_euclid : (buildingDist b md (ρ z) z_t) ^ 2 =
    t * (buildingDist b md (ρ z) x) ^ 2 +
    (1 - t) * (buildingDist b md (ρ z) y) ^ 2 -
    t * (1 - t) * (buildingDist b md x y) ^ 2 :=
    euclidean_identity_in_apartment b md coord dist_eq_norm coord_geodesic
      x y (ρ z) z_t t ht0 ht1 hzt_x hzt_y A hρzA hxA hyA hztA
  rw [hρ_isom, h_euclid]
  have h_dim_x : buildingDist b md (ρ z) x ≤ buildingDist b md z x := by
    have h := hρ_nonincr z x; rw [hρ_fix_x] at h; exact h
  have h_dim_y : buildingDist b md (ρ z) y ≤ buildingDist b md z y := by
    have h := hρ_nonincr z y; rw [hρ_fix_y] at h; exact h
  have hρx_sq : (buildingDist b md (ρ z) x) ^ 2 ≤
    (buildingDist b md z x) ^ 2 :=
    pow_le_pow_left₀ (buildingDist_nonneg b md (ρ z) x) h_dim_x 2
  have hρy_sq : (buildingDist b md (ρ z) y) ^ 2 ≤
    (buildingDist b md z y) ^ 2 :=
    pow_le_pow_left₀ (buildingDist_nonneg b md (ρ z) y) h_dim_y 2
  have h1 : t * (buildingDist b md (ρ z) x) ^ 2 ≤
    t * (buildingDist b md z x) ^ 2 :=
    mul_le_mul_of_nonneg_left hρx_sq ht0
  have h2 : (1 - t) * (buildingDist b md (ρ z) y) ^ 2 ≤
    (1 - t) * (buildingDist b md z y) ^ 2 :=
    mul_le_mul_of_nonneg_left hρy_sq (sub_nonneg.mpr ht1)
  linarith



-- created on 2026-10-23
-- updated on 2026-10-26
