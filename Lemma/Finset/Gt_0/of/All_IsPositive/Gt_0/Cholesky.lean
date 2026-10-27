import Initialize.Tactic.Attr.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
open Finset Function
open scoped ComplexOrder

variable {n : ℕ}


private abbrev choleskyGt_w (t : Fin n) (ξ : Fin n → ℝ) (i : Fin n) : ℝ :=
  if i = t then 1 else ξ i

private abbrev choleskyGt_S (L : Matrix (Fin n) (Fin n) ℝ) (t : Fin n) (ξ : Fin n → ℝ) (c : Fin n) : ℝ :=
  ∑ i ∈ Icc c t, choleskyGt_w t ξ i * L i c

/-- Prefix inner product of rows `i` and `j` on columns `< t`. -/
private def choleskyGt_ip (L : Matrix (Fin n) (Fin n) ℝ) (t i j : Fin n) : ℝ :=
  ∑ c ∈ (Iio t).filter (fun c => c ≤ min i j), L i c * L j c

/-- The quadratic form from the Cholesky diagonal step. -/
private abbrev choleskyGt_Qsum (L : Matrix (Fin n) (Fin n) ℝ) (t : Fin n) (ξ : Fin n → ℝ) : ℝ :=
  ∑ i ∈ Iio t,
    (ξ i ^ 2 * ∑ k ∈ Iic i, L i k ^ 2 +
      2 * ξ i * ∑ j ∈ Ioc i t, choleskyGt_w t ξ j * ∑ k ∈ Iic i, L j k * L i k)

private lemma choleskyGt_filter_Iic_eq_Icc (t : Fin n) {c : Fin n} (_ : c ≤ t) :
  (Iic t).filter (fun i => c ≤ i) = Icc c t := by
  ext i
  simp only [mem_filter, mem_Iic, mem_Icc]
  exact ⟨fun ⟨hit, hci⟩ => ⟨hci, hit⟩, fun ⟨hci, hit⟩ => ⟨hit, hci⟩⟩

private lemma choleskyGt_ip_comm (L : Matrix (Fin n) (Fin n) ℝ) (t i j : Fin n) :
  choleskyGt_ip L t i j = choleskyGt_ip L t j i := by
  unfold choleskyGt_ip
  rw [min_comm i j]
  refine sum_congr rfl fun _ _ => mul_comm _ _

private lemma choleskyGt_ip_diag_of_lt
  (L : Matrix (Fin n) (Fin n) ℝ) {t i : Fin n} (hi : i < t) :
  choleskyGt_ip L t i i = ∑ k ∈ Iic i, L i k ^ 2 := by
  unfold choleskyGt_ip
  rw [min_self]
  refine sum_congr ?_ fun _ _ => (sq _).symm
  ext c
  simp only [mem_filter, mem_Iio, mem_Iic]
  exact ⟨And.right, fun hc => ⟨lt_of_le_of_lt hc hi, hc⟩⟩

private lemma choleskyGt_ip_of_le_of_lt
  (L : Matrix (Fin n) (Fin n) ℝ) {t i j : Fin n}
  (hij : i ≤ j) (hi : i < t) :
  choleskyGt_ip L t i j = ∑ k ∈ Iic i, L i k * L j k := by
  unfold choleskyGt_ip
  rw [min_eq_left hij]
  refine sum_congr ?_ fun _ _ => rfl
  ext c
  simp only [mem_filter, mem_Iio, mem_Iic]
  exact ⟨And.right, fun hc => ⟨lt_of_le_of_lt hc hi, hc⟩⟩

private lemma choleskyGt_ip_tt
  (L : Matrix (Fin n) (Fin n) ℝ) (t : Fin n) :
  choleskyGt_ip L t t t = ∑ c ∈ Iio t, L t c ^ 2 := by
  unfold choleskyGt_ip
  rw [min_self]
  refine sum_congr ?_ fun _ _ => (sq _).symm
  ext c
  simp only [mem_filter, mem_Iio]
  exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, le_of_lt h⟩⟩

/-- Split `Iic t = insert t (Iio t)`. -/
private lemma choleskyGt_Iic_eq_insert_Iio (t : Fin n) :
  Iic t = insert t (Iio t) := by
  ext i
  simp only [mem_Iic, mem_insert, mem_Iio]
  exact ⟨fun h => (lt_or_eq_of_le h).elim Or.inr Or.inl,
    fun h => h.elim (fun h => h ▸ le_rfl) le_of_lt⟩

/-- Symmetric double sum: diagonal + twice strict upper triangle. -/
private lemma choleskyGt_sum_sum_symm
  (t : Fin n) (g : Fin n → Fin n → ℝ) (hsymm : ∀ i j, g i j = g j i) :
  ∑ i ∈ Iio t, ∑ j ∈ Iio t, g i j =
    ∑ i ∈ Iio t, g i i + 2 * ∑ i ∈ Iio t, ∑ j ∈ Ioo i t, g i j := by
  have hsplit :
    ∑ i ∈ Iio t, ∑ j ∈ Iio t, g i j =
      ∑ i ∈ Iio t, g i i + ∑ i ∈ Iio t, ∑ j ∈ Iio t \ {i}, g i j := calc
      _ = ∑ i ∈ Iio t, (g i i + ∑ j ∈ Iio t \ {i}, g i j) := by
        apply sum_congr rfl
        intro i hi
        have hunion : Iio t = {i} ∪ (Iio t \ {i}) := by
          ext j
          simp only [mem_union, mem_singleton, mem_sdiff]
          exact ⟨fun hj =>
            if hji : j = i then Or.inl hji else Or.inr ⟨hj, hji⟩,
            fun h => h.elim (fun hji => hji ▸ hi) And.left⟩
        have hdisj : Disjoint ({i} : Finset (Fin n)) (Iio t \ {i}) := by
          simp [disjoint_singleton_left]
        conv_lhs => rw [hunion]
        rw [sum_union hdisj, sum_singleton]
      _ = ∑ i ∈ Iio t, g i i + ∑ i ∈ Iio t, ∑ j ∈ Iio t \ {i}, g i j :=
        sum_add_distrib
  have hupper_lower :
    ∑ i ∈ Iio t, ∑ j ∈ Iio t \ {i}, g i j =
      ∑ i ∈ Iio t, ∑ j ∈ Ioo i t, g i j +
        ∑ i ∈ Iio t, ∑ j ∈ Iio i, g i j := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i hi => ?_
    have hpartition : Iio t \ {i} = Ioo i t ∪ Iio i := by
      ext j
      simp only [mem_sdiff, mem_Iio, mem_singleton, mem_union, mem_Ioo]
      constructor
      ·
        intro ⟨hjt, hne⟩
        exact (lt_or_gt_of_ne hne).elim (fun h => Or.inr h)
          fun h => Or.inl ⟨h, hjt⟩
      ·
        rintro (⟨hij, hjt⟩ | hji)
        · exact ⟨hjt, ne_of_gt hij⟩
        · exact ⟨lt_trans hji (mem_Iio.mp hi), ne_of_lt hji⟩
    have hdisj : Disjoint (Ioo i t) (Iio i) :=
      disjoint_left.mpr fun j hj hj' =>
        lt_asymm (mem_Ioo.mp hj).1 (mem_Iio.mp hj')
    rw [hpartition, sum_union hdisj]
  have hswap :
    ∑ i ∈ Iio t, ∑ j ∈ Iio i, g i j =
      ∑ i ∈ Iio t, ∑ j ∈ Ioo i t, g i j := calc
      _ = ∑ i ∈ Iio t, ∑ j ∈ Iio t, if j < i then g i j else 0 := by
        refine sum_congr rfl fun i hi => ?_
        have hset : (Iio t).filter (fun j => j < i) = Iio i := by
          ext j
          simp only [mem_filter, mem_Iio]
          exact ⟨And.right, fun hji => ⟨lt_trans hji (mem_Iio.mp hi), hji⟩⟩
        rw [← sum_filter, hset]
      _ = ∑ j ∈ Iio t, ∑ i ∈ Iio t, if j < i then g i j else 0 := sum_comm
      _ = ∑ j ∈ Iio t, ∑ i ∈ Ioo j t, g i j := by
        refine sum_congr rfl fun j _ => ?_
        have hset : (Iio t).filter (fun i => j < i) = Ioo j t := by
          ext i
          simp only [mem_filter, mem_Iio, mem_Ioo]
          exact ⟨fun ⟨hit, hji⟩ => ⟨hji, hit⟩, fun ⟨hji, hit⟩ => ⟨hit, hji⟩⟩
        rw [← sum_filter, hset]
      _ = ∑ j ∈ Iio t, ∑ i ∈ Ioo j t, g j i :=
        sum_congr rfl fun j _ => sum_congr rfl fun i _ => hsymm _ _
      _ = ∑ i ∈ Iio t, ∑ j ∈ Ioo i t, g i j := rfl
  rw [hsplit, hupper_lower, hswap]
  ring

/-- `∑_c S_c² = ∑_{i≤t} ∑_{j≤t} choleskyGt_wᵢ choleskyGt_wⱼ ⟨rowᵢ, rowⱼ⟩_<t`. -/
private lemma choleskyGt_sum_S_sq
  (L : Matrix (Fin n) (Fin n) ℝ) (t : Fin n) (ξ : Fin n → ℝ) :
  ∑ c ∈ Iio t, choleskyGt_S L t ξ c ^ 2 =
    ∑ i ∈ Iic t, ∑ j ∈ Iic t, choleskyGt_w t ξ i * choleskyGt_w t ξ j * choleskyGt_ip L t i j := by
  have h1 :
    ∑ c ∈ Iio t, choleskyGt_S L t ξ c ^ 2 =
      ∑ c ∈ Iio t, ∑ i ∈ Icc c t, ∑ j ∈ Icc c t,
        (choleskyGt_w t ξ i * L i c) * (choleskyGt_w t ξ j * L j c) := by
    refine sum_congr rfl fun c _ => ?_
    dsimp [choleskyGt_S]
    rw [sq, ← sum_mul_sum]
  rw [h1]
  have h2 :
    ∀ c ∈ Iio t,
      ∑ i ∈ Icc c t, ∑ j ∈ Icc c t,
          (choleskyGt_w t ξ i * L i c) * (choleskyGt_w t ξ j * L j c) =
        ∑ i ∈ Iic t, ∑ j ∈ Iic t,
          if c ≤ i ∧ c ≤ j then
            (choleskyGt_w t ξ i * L i c) * (choleskyGt_w t ξ j * L j c)
          else 0 := by
    intro c hc
    have hct : c ≤ t := (mem_Iio.mp hc).le
    have hI : (Iic t).filter (fun i => c ≤ i) = Icc c t := choleskyGt_filter_Iic_eq_Icc t hct
    calc
      _ = ∑ i ∈ (Iic t).filter (fun i => c ≤ i),
          ∑ j ∈ (Iic t).filter (fun j => c ≤ j),
            (choleskyGt_w t ξ i * L i c) * (choleskyGt_w t ξ j * L j c) := by rw [hI]
      _ = ∑ i ∈ Iic t, if c ≤ i then
          ∑ j ∈ Iic t, if c ≤ j then
            (choleskyGt_w t ξ i * L i c) * (choleskyGt_w t ξ j * L j c) else 0 else 0 := by
        simp_rw [sum_filter]
      _ = ∑ i ∈ Iic t, ∑ j ∈ Iic t,
          if c ≤ i ∧ c ≤ j then
            (choleskyGt_w t ξ i * L i c) * (choleskyGt_w t ξ j * L j c) else 0 := by
        refine sum_congr rfl fun i _ => ?_
        if hi : c ≤ i then
          simp [hi]
        else
          simp [hi]
  calc
    _ = ∑ c ∈ Iio t, ∑ i ∈ Iic t, ∑ j ∈ Iic t,
        if c ≤ i ∧ c ≤ j then
          (choleskyGt_w t ξ i * L i c) * (choleskyGt_w t ξ j * L j c) else 0 :=
      sum_congr rfl h2
    _ = ∑ i ∈ Iic t, ∑ j ∈ Iic t, ∑ c ∈ Iio t,
        if c ≤ i ∧ c ≤ j then
          (choleskyGt_w t ξ i * L i c) * (choleskyGt_w t ξ j * L j c) else 0 := by
      rw [sum_comm]
      refine sum_congr rfl fun i _ => ?_
      rw [sum_comm]
    _ = ∑ i ∈ Iic t, ∑ j ∈ Iic t,
        ∑ c ∈ (Iio t).filter (fun c => c ≤ i ∧ c ≤ j),
          (choleskyGt_w t ξ i * L i c) * (choleskyGt_w t ξ j * L j c) := by
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
      simp_rw [sum_filter]
    _ = ∑ i ∈ Iic t, ∑ j ∈ Iic t, choleskyGt_w t ξ i * choleskyGt_w t ξ j * choleskyGt_ip L t i j := by
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
      have hmin : (Iio t).filter (fun c => c ≤ i ∧ c ≤ j) =
        (Iio t).filter (fun c => c ≤ min i j) := by
        ext c; simp only [mem_filter, le_min_iff]
      unfold choleskyGt_ip
      rw [hmin]
      calc
        _ = ∑ c ∈ (Iio t).filter (fun c => c ≤ min i j),
            choleskyGt_w t ξ i * choleskyGt_w t ξ j * (L i c * L j c) := by
          refine sum_congr rfl fun _ _ => by ring
        _ = choleskyGt_w t ξ i * choleskyGt_w t ξ j *
            ∑ c ∈ (Iio t).filter (fun c => c ≤ min i j), L i c * L j c := by
          simp_rw [mul_sum]

/-- Expand the Gram sum into choleskyGt_Qsum + `‖row_t‖²_<t`. -/
private lemma choleskyGt_gram_eq_Qsum_add
  (L : Matrix (Fin n) (Fin n) ℝ) (t : Fin n) (ξ : Fin n → ℝ) :
  ∑ i ∈ Iic t, ∑ j ∈ Iic t, choleskyGt_w t ξ i * choleskyGt_w t ξ j * choleskyGt_ip L t i j =
    choleskyGt_Qsum L t ξ + choleskyGt_ip L t t t := by
  set s := Iio t
  have ht : t ∉ s := by
    dsimp [s]
    simp [mem_Iio]
  have hw_t : choleskyGt_w t ξ t = 1 := by simp [choleskyGt_w]
  have hw_s : ∀ i ∈ s, choleskyGt_w t ξ i = ξ i := by
    intro i hi
    simp [choleskyGt_w, ne_of_lt (mem_Iio.mp hi)]
  rw [choleskyGt_Iic_eq_insert_Iio]
  set f : Fin n → Fin n → ℝ := fun i j => choleskyGt_w t ξ i * choleskyGt_w t ξ j * choleskyGt_ip L t i j
  change ∑ i ∈ insert t s, ∑ j ∈ insert t s, f i j = choleskyGt_Qsum L t ξ + choleskyGt_ip L t t t
  rw [sum_insert ht, sum_insert ht]
  have hftt : f t t = choleskyGt_ip L t t t := by
    dsimp [f]; rw [hw_t]; ring
  have hftj : ∀ j ∈ s, f t j = ξ j * choleskyGt_ip L t t j := by
    intro j hj
    dsimp [f]; rw [hw_t, one_mul, hw_s j hj]
  have hinner :
    ∀ i ∈ s, ∑ j ∈ insert t s, f i j = f i t + ∑ j ∈ s, f i j := by
    intro i _; rw [sum_insert ht]
  -- After `sum_insert` twice: `f t t + ∑ j ∈ s, f t j + ∑ i ∈ s, ∑ j ∈ insert t s, f i j`
  have hrest :
    ∑ i ∈ s, ∑ j ∈ insert t s, f i j =
      ∑ i ∈ s, f i t + ∑ i ∈ s, ∑ j ∈ s, f i j := calc
      _ = ∑ i ∈ s, (f i t + ∑ j ∈ s, f i j) :=
        sum_congr rfl fun i hi => hinner i hi
      _ = ∑ i ∈ s, f i t + ∑ i ∈ s, ∑ j ∈ s, f i j := sum_add_distrib
  rw [hrest]
  have hfit : ∀ i ∈ s, f i t = ξ i * choleskyGt_ip L t i t := by
    intro i hi
    dsimp [f]; rw [hw_t, mul_one, hw_s i hi]
  have hfij : ∀ i ∈ s, ∀ j ∈ s, f i j = ξ i * ξ j * choleskyGt_ip L t i j := by
    intro i hi j hj
    dsimp [f]; rw [hw_s i hi, hw_s j hj]
  have hcross :
    ∑ j ∈ s, ξ j * choleskyGt_ip L t t j = ∑ i ∈ s, ξ i * choleskyGt_ip L t i t :=
    sum_congr rfl fun j _ => by rw [choleskyGt_ip_comm]
  -- Parentheses from `hrest`: `f t t + ∑ f t + (∑ f i t + ∑∑ f i j)`
  rw [← add_assoc, hftt]
  have hftj' : ∑ j ∈ s, f t j = ∑ j ∈ s, ξ j * choleskyGt_ip L t t j :=
    sum_congr rfl fun j hj => hftj j hj
  have hfit' : ∑ i ∈ s, f i t = ∑ i ∈ s, ξ i * choleskyGt_ip L t i t :=
    sum_congr rfl fun i hi => hfit i hi
  have hfij' :
    ∑ i ∈ s, ∑ j ∈ s, f i j = ∑ i ∈ s, ∑ j ∈ s, ξ i * ξ j * choleskyGt_ip L t i j :=
    sum_congr rfl fun i hi => sum_congr rfl fun j hj => hfij i hi j hj
  rw [hftj', hfit', hfij']
  have hbilin :
    ∑ i ∈ s, ∑ j ∈ s, ξ i * ξ j * choleskyGt_ip L t i j =
      ∑ i ∈ s, ξ i ^ 2 * choleskyGt_ip L t i i +
        2 * ∑ i ∈ s, ∑ j ∈ Ioo i t, ξ i * ξ j * choleskyGt_ip L t i j := by
    let g : Fin n → Fin n → ℝ := fun i j => ξ i * ξ j * choleskyGt_ip L t i j
    have hsymm : ∀ i j, g i j = g j i := by
      intro i j
      dsimp [g]
      rw [choleskyGt_ip_comm L t i j]
      ring
    have h := choleskyGt_sum_sum_symm (t := t) (g := g) hsymm
    simpa [s, g, sq, mul_assoc] using h
  have hsplit :
    ∀ i ∈ Iio t,
      ∑ j ∈ Ioc i t, choleskyGt_w t ξ j * ∑ k ∈ Iic i, L j k * L i k =
        ∑ j ∈ Ioo i t, ξ j * choleskyGt_ip L t i j + choleskyGt_ip L t i t := by
    intro i hi
    have hit : i < t := mem_Iio.mp hi
    have hIoc : Ioc i t = insert t (Ioo i t) := by
      ext j
      simp only [mem_Ioc, mem_insert, mem_Ioo]
      constructor
      ·
        intro ⟨hij, hjt⟩
        exact (lt_or_eq_of_le hjt).elim (fun h => Or.inr ⟨hij, h⟩) Or.inl
      ·
        rintro (rfl | ⟨hij, hjt⟩)
        · exact ⟨hit, le_rfl⟩
        · exact ⟨hij, hjt.le⟩
    rw [hIoc, sum_insert (by simp [mem_Ioo])]
    simp only [hw_t]
    have ht_term : ∑ k ∈ Iic i, L t k * L i k = choleskyGt_ip L t i t := by
      rw [choleskyGt_ip_of_le_of_lt L (le_of_lt hit) hit]
      refine sum_congr rfl fun _ _ => mul_comm _ _
    have hj_term :
      ∑ j ∈ Ioo i t, choleskyGt_w t ξ j * ∑ k ∈ Iic i, L j k * L i k =
        ∑ j ∈ Ioo i t, ξ j * choleskyGt_ip L t i j := by
      refine sum_congr rfl fun j hj => ?_
      have hjt : j < t := (mem_Ioo.mp hj).2
      have hij : i < j := (mem_Ioo.mp hj).1
      simp only [choleskyGt_w, ne_of_lt hjt, ite_false]
      rw [choleskyGt_ip_of_le_of_lt L hij.le hit]
      refine congr_arg (fun x => ξ j * x) ?_
      refine sum_congr rfl fun _ _ => mul_comm _ _
    rw [hj_term, ht_term, one_mul, add_comm]
  have hdiag :
    ∀ i ∈ Iio t, ∑ k ∈ Iic i, L i k ^ 2 = choleskyGt_ip L t i i := by
    intro i hi
    exact (choleskyGt_ip_diag_of_lt L (mem_Iio.mp hi)).symm
  have hQ :
    choleskyGt_Qsum L t ξ =
      ∑ i ∈ s, ξ i ^ 2 * choleskyGt_ip L t i i +
        2 * ∑ i ∈ s, ∑ j ∈ Ioo i t, ξ i * ξ j * choleskyGt_ip L t i j +
        2 * ∑ i ∈ s, ξ i * choleskyGt_ip L t i t := by
    dsimp [choleskyGt_Qsum, s]
    have hterm :
      ∀ i ∈ Iio t,
        ξ i ^ 2 * ∑ k ∈ Iic i, L i k ^ 2 +
            2 * ξ i * ∑ j ∈ Ioc i t, choleskyGt_w t ξ j * ∑ k ∈ Iic i, L j k * L i k =
          ξ i ^ 2 * choleskyGt_ip L t i i +
            2 * (∑ j ∈ Ioo i t, ξ i * ξ j * choleskyGt_ip L t i j) +
            2 * (ξ i * choleskyGt_ip L t i t) := by
      intro i hi
      rw [hdiag i hi, hsplit i hi, mul_add]
      have hrearr :
        2 * ξ i * ∑ j ∈ Ioo i t, ξ j * choleskyGt_ip L t i j =
          2 * ∑ j ∈ Ioo i t, ξ i * ξ j * choleskyGt_ip L t i j := by
        rw [mul_assoc, mul_sum]
        congr 1
        refine sum_congr rfl fun j _ => by ring
      -- normalize `2 * ξ i * choleskyGt_ip` to `2 * (ξ i * choleskyGt_ip)`
      rw [hrearr, mul_assoc (2 : ℝ) (ξ i)]
      ring
    calc
      _ = ∑ i ∈ Iio t,
          (ξ i ^ 2 * choleskyGt_ip L t i i +
            2 * ∑ j ∈ Ioo i t, ξ i * ξ j * choleskyGt_ip L t i j +
            2 * (ξ i * choleskyGt_ip L t i t)) :=
        sum_congr rfl hterm
      _ = ∑ i ∈ Iio t, ξ i ^ 2 * choleskyGt_ip L t i i +
          ∑ i ∈ Iio t, 2 * ∑ j ∈ Ioo i t, ξ i * ξ j * choleskyGt_ip L t i j +
          ∑ i ∈ Iio t, 2 * (ξ i * choleskyGt_ip L t i t) := by
        simp_rw [sum_add_distrib]
      _ = ∑ i ∈ s, ξ i ^ 2 * choleskyGt_ip L t i i +
          2 * ∑ i ∈ s, ∑ j ∈ Ioo i t, ξ i * ξ j * choleskyGt_ip L t i j +
          2 * ∑ i ∈ s, ξ i * choleskyGt_ip L t i t := by
        simp only [s]
        rw [Eq.symm
            (mul_sum (s := Iio t) (a := (2 : ℝ))
              (f := fun i => ∑ j ∈ Ioo i t, ξ i * ξ j * choleskyGt_ip L t i j)),
          Eq.symm
            (mul_sum (s := Iio t) (a := (2 : ℝ))
              (f := fun i => ξ i * choleskyGt_ip L t i t))]
  rw [hcross, hbilin, hQ]
  ring

/--
Column expansion: `choleskyGt_Qsum ξ = ∑_{c < t} S_c(ξ)² - ∑_{c < t} L_{t c}²`.
-/
private lemma choleskyGt_Qsum_eq
  (L : Matrix (Fin n) (Fin n) ℝ) (t : Fin n) (ξ : Fin n → ℝ) :
  choleskyGt_Qsum L t ξ =
    (∑ c ∈ Iio t, choleskyGt_S L t ξ c ^ 2) - ∑ c ∈ Iio t, L t c ^ 2 := by
  have hgram := choleskyGt_gram_eq_Qsum_add L t ξ
  have hS := choleskyGt_sum_S_sq L t ξ
  have htt := choleskyGt_ip_tt L t
  calc
    _ = ∑ i ∈ Iic t, ∑ j ∈ Iic t, choleskyGt_w t ξ i * choleskyGt_w t ξ j * choleskyGt_ip L t i j -
      choleskyGt_ip L t t t := by linarith [hgram]
    _ = ∑ c ∈ Iio t, choleskyGt_S L t ξ c ^ 2 - choleskyGt_ip L t t t := by rw [hS]
    _ = ∑ c ∈ Iio t, choleskyGt_S L t ξ c ^ 2 - ∑ c ∈ Iio t, L t c ^ 2 := by rw [htt]

private lemma choleskyGt_rank_lt
  {t c i : Fin n} (hip : c < i ∧ i ≤ t) :
  t.val - i.val < t.val - c.val :=
  Nat.sub_lt_sub_left (lt_of_lt_of_le hip.1 hip.2) hip.1

/-- Back-substitution: `choleskyGt_optξ` makes every column residual `S_c` vanish. -/
noncomputable def choleskyGt_optξ (L : Matrix (Fin n) (Fin n) ℝ) (t : Fin n) : Fin n → ℝ :=
  WellFounded.fix
    (InvImage.wf (fun c : Fin n => (t.val : ℕ) - c.val) Nat.lt_wfRel.wf) fun c ih =>
    if _ : c < t then
      -(∑ i ∈ (Ioc c t).attach,
          (if i.1 = t then (1 : ℝ)
            else ih i.1 (choleskyGt_rank_lt (mem_Ioc.mp i.property))) * L i.1 c) / L c c
    else
      0

private lemma choleskyGt_optξ_lt
  (L : Matrix (Fin n) (Fin n) ℝ) (t : Fin n) {c : Fin n} (hc : c < t) :
  choleskyGt_optξ L t c = -(∑ i ∈ Ioc c t, choleskyGt_w t (choleskyGt_optξ L t) i * L i c) / L c c := by
  conv_lhs => rw [choleskyGt_optξ, WellFounded.fix_eq]
  dsimp only
  simp only [hc, ↓reduceDIte]
  refine congr_arg (fun x => -x / L c c) ?_
  rw [← sum_attach (f := fun i => choleskyGt_w t (choleskyGt_optξ L t) i * L i c)]
  refine sum_congr rfl fun i _ => ?_
  dsimp [choleskyGt_w]
  split_ifs <;> rfl

private lemma choleskyGt_S_optξ_eq_zero
  (L : Matrix (Fin n) (Fin n) ℝ) (t : Fin n)
  (h₀ : ∀ i, i < t → 0 < L i i) {c : Fin n} (hc : c ∈ Iio t) :
  choleskyGt_S L t (choleskyGt_optξ L t) c = 0 := by
  have hct : c < t := mem_Iio.mp hc
  have hne : L c c ≠ 0 := ne_of_gt (h₀ c hct)
  have hIcc : Icc c t = insert c (Ioc c t) := by
    ext i
    simp only [mem_Icc, mem_insert, mem_Ioc]
    constructor
    ·
      intro ⟨hci, hit⟩
      exact (eq_or_lt_of_le hci).elim (fun h => Or.inl h.symm) fun h => Or.inr ⟨h, hit⟩
    ·
      rintro (rfl | ⟨hci, hit⟩)
      · exact ⟨le_rfl, hct.le⟩
      · exact ⟨hci.le, hit⟩
  dsimp [choleskyGt_S]
  rw [hIcc, sum_insert (by simp [mem_Ioc])]
  have hc_ne_t : c ≠ t := ne_of_lt hct
  simp only [choleskyGt_w, hc_ne_t, ite_false]
  rw [choleskyGt_optξ_lt L t hct]
  field_simp
  ring


private abbrev choleskyGtC_w (t : Fin n) (ξ : Fin n → ℂ) (i : Fin n) : ℂ :=
  if i = t then 1 else ξ i

private abbrev choleskyGtC_S (L : Matrix (Fin n) (Fin n) ℂ) (t : Fin n) (ξ : Fin n → ℂ) (c : Fin n) : ℂ :=
  ∑ i ∈ Icc c t, choleskyGtC_w t ξ i * L i c

/-- Prefix Hermitian inner product of rows `i` and `j` on columns `< t`. -/
private def choleskyGtC_ip (L : Matrix (Fin n) (Fin n) ℂ) (t i j : Fin n) : ℂ :=
  ∑ c ∈ (Iio t).filter (fun c => c ≤ min i j), star (L i c) * L j c

/--
The quadratic form from the Cholesky diagonal step over ℂ.
Cross terms use `star (L i) * L j` so that `choleskyGtC_Qsum = ∑ ‖choleskyGtC_S‖² - ∑ ‖L_t‖²`.
-/
noncomputable abbrev choleskyGtC_Qsum
  (L : Matrix (Fin n) (Fin n) ℂ) (t : Fin n) (ξ : Fin n → ℂ) : ℝ :=
  ∑ i ∈ Iio t,
    (‖ξ i‖ ^ 2 * ∑ k ∈ Iic i, ‖L i k‖ ^ 2 +
      2 * RCLike.re (star (ξ i) *
        ∑ j ∈ Ioc i t, choleskyGtC_w t ξ j * ∑ k ∈ Iic i, star (L i k) * L j k))

/-- Back-substitution for the complex residual. -/
noncomputable def choleskyGtC_optξ (L : Matrix (Fin n) (Fin n) ℂ) (t : Fin n) : Fin n → ℂ :=
  WellFounded.fix
    (InvImage.wf (fun c : Fin n => (t.val : ℕ) - c.val) Nat.lt_wfRel.wf) fun c ih =>
    if _ : c < t then
      -(∑ i ∈ (Ioc c t).attach,
          (if i.1 = t then (1 : ℂ)
            else ih i.1 (choleskyGt_rank_lt (mem_Ioc.mp i.property))) * L i.1 c) / L c c
    else
      0

private lemma choleskyGtC_optξ_lt
  (L : Matrix (Fin n) (Fin n) ℂ) (t : Fin n) {c : Fin n} (hc : c < t) :
  choleskyGtC_optξ L t c = -(∑ i ∈ Ioc c t, choleskyGtC_w t (choleskyGtC_optξ L t) i * L i c) / L c c := by
  conv_lhs => rw [choleskyGtC_optξ, WellFounded.fix_eq]
  dsimp only
  simp only [hc, ↓reduceDIte]
  refine congr_arg (fun x => -x / L c c) ?_
  rw [← sum_attach (f := fun i => choleskyGtC_w t (choleskyGtC_optξ L t) i * L i c)]
  refine sum_congr rfl fun i _ => ?_
  dsimp [choleskyGtC_w]
  split_ifs <;> rfl

private lemma choleskyGtC_S_optξ_eq_zero
  (L : Matrix (Fin n) (Fin n) ℂ) (t : Fin n)
  (h₀ : ∀ i, i < t → 0 < L i i) {c : Fin n} (hc : c ∈ Iio t) :
  choleskyGtC_S L t (choleskyGtC_optξ L t) c = 0 := by
  have hct : c < t := mem_Iio.mp hc
  have hne : L c c ≠ 0 := by
    intro h
    have hpos := h₀ c hct
    simp [h] at hpos
  have hIcc : Icc c t = insert c (Ioc c t) := by
    ext i
    simp only [mem_Icc, mem_insert, mem_Ioc]
    constructor
    ·
      intro ⟨hci, hit⟩
      exact (eq_or_lt_of_le hci).elim (fun h => Or.inl h.symm) fun h => Or.inr ⟨h, hit⟩
    ·
      rintro (rfl | ⟨hci, hit⟩)
      · exact ⟨le_rfl, hct.le⟩
      · exact ⟨hci.le, hit⟩
  dsimp [choleskyGtC_S]
  rw [hIcc, sum_insert (by simp [mem_Ioc])]
  have hc_ne_t : c ≠ t := ne_of_lt hct
  simp only [choleskyGtC_w, hc_ne_t, ite_false]
  rw [choleskyGtC_optξ_lt L t hct]
  field_simp
  ring

private lemma choleskyGtC_filter_Iic_eq_Icc (t : Fin n) {c : Fin n} (_ : c ≤ t) :
  (Iic t).filter (fun i => c ≤ i) = Icc c t := by
  ext i
  simp only [mem_filter, mem_Iic, mem_Icc]
  exact ⟨fun ⟨hit, hci⟩ => ⟨hci, hit⟩, fun ⟨hci, hit⟩ => ⟨hit, hci⟩⟩

private lemma choleskyGtC_ip_star (L : Matrix (Fin n) (Fin n) ℂ) (t i j : Fin n) :
  choleskyGtC_ip L t j i = star (choleskyGtC_ip L t i j) := by
  unfold choleskyGtC_ip
  rw [min_comm j i]
  refine Eq.trans ?_ (Eq.symm (map_sum (starRingEnd ℂ)
    (fun c => star (L i c) * L j c) ((Iio t).filter (fun c => c ≤ min i j))))
  refine sum_congr rfl fun c _ => ?_
  change (starRingEnd ℂ) (L j c) * L i c =
    (starRingEnd ℂ) ((starRingEnd ℂ) (L i c) * L j c)
  rw [map_mul (starRingEnd ℂ), starRingEnd_self_apply, mul_comm]

private lemma choleskyGtC_ip_diag_of_lt
  (L : Matrix (Fin n) (Fin n) ℂ) {t i : Fin n} (hi : i < t) :
  choleskyGtC_ip L t i i = ((∑ k ∈ Iic i, ‖L i k‖ ^ 2 : ℝ) : ℂ) := by
  unfold choleskyGtC_ip
  rw [min_self]
  have hset : (Iio t).filter (fun c => c ≤ i) = Iic i := by
    ext c
    simp only [mem_filter, mem_Iio, mem_Iic]
    exact ⟨And.right, fun hc => ⟨lt_of_le_of_lt hc hi, hc⟩⟩
  rw [hset]
  have hk : ∀ k ∈ Iic i, star (L i k) * L i k = ((‖L i k‖ ^ 2 : ℝ) : ℂ) := by
    intro k _
    rw [RCLike.star_def, RCLike.conj_mul]
    norm_cast
  rw [sum_congr rfl hk]
  exact (Complex.ofReal_sum (Iic i) (fun k => ‖L i k‖ ^ 2)).symm

private lemma choleskyGtC_ip_of_le_of_lt
  (L : Matrix (Fin n) (Fin n) ℂ) {t i j : Fin n}
  (hij : i ≤ j) (hi : i < t) :
  choleskyGtC_ip L t i j = ∑ k ∈ Iic i, star (L i k) * L j k := by
  unfold choleskyGtC_ip
  rw [min_eq_left hij]
  refine sum_congr ?_ fun _ _ => rfl
  ext c
  simp only [mem_filter, mem_Iio, mem_Iic]
  exact ⟨And.right, fun hc => ⟨lt_of_le_of_lt hc hi, hc⟩⟩

private lemma choleskyGtC_ip_tt
  (L : Matrix (Fin n) (Fin n) ℂ) (t : Fin n) :
  choleskyGtC_ip L t t t = ((∑ c ∈ Iio t, ‖L t c‖ ^ 2 : ℝ) : ℂ) := by
  unfold choleskyGtC_ip
  rw [min_self]
  have hset : (Iio t).filter (fun c => c ≤ t) = Iio t := by
    ext c
    simp only [mem_filter, mem_Iio]
    exact ⟨And.left, fun h => ⟨h, le_of_lt h⟩⟩
  rw [hset]
  have hk : ∀ c ∈ Iio t, star (L t c) * L t c = ((‖L t c‖ ^ 2 : ℝ) : ℂ) := by
    intro c _
    rw [RCLike.star_def, RCLike.conj_mul]
    norm_cast
  rw [sum_congr rfl hk]
  exact (Complex.ofReal_sum (Iio t) (fun c => ‖L t c‖ ^ 2)).symm

private lemma choleskyGtC_Iic_eq_insert_Iio (t : Fin n) :
  Iic t = insert t (Iio t) := by
  ext i
  simp only [mem_Iic, mem_insert, mem_Iio]
  exact ⟨fun h => (lt_or_eq_of_le h).elim Or.inr Or.inl,
    fun h => h.elim (fun h => h ▸ le_rfl) le_of_lt⟩

private lemma choleskyGtC_re_add_star (z : ℂ) :
  RCLike.re (z + star z) = 2 * RCLike.re z := by
  rw [RCLike.star_def, map_add, RCLike.conj_re]
  ring

private lemma choleskyGtC_sum_sum_herm
  (t : Fin n) (g : Fin n → Fin n → ℂ) (hherm : ∀ i j, g j i = star (g i j)) :
  RCLike.re (∑ i ∈ Iio t, ∑ j ∈ Iio t, g i j) =
    ∑ i ∈ Iio t, RCLike.re (g i i) +
      2 * ∑ i ∈ Iio t, ∑ j ∈ Ioo i t, RCLike.re (g i j) := by
  have hsplit :
    ∑ i ∈ Iio t, ∑ j ∈ Iio t, g i j =
      ∑ i ∈ Iio t, g i i + ∑ i ∈ Iio t, ∑ j ∈ Iio t \ {i}, g i j := calc
      _ = ∑ i ∈ Iio t, (g i i + ∑ j ∈ Iio t \ {i}, g i j) := by
        apply sum_congr rfl
        intro i hi
        have hunion : Iio t = {i} ∪ (Iio t \ {i}) := by
          ext j
          simp only [mem_union, mem_singleton, mem_sdiff]
          exact ⟨fun hj =>
            if hji : j = i then Or.inl hji else Or.inr ⟨hj, hji⟩,
            fun h => h.elim (fun hji => hji ▸ hi) And.left⟩
        have hdisj : Disjoint ({i} : Finset (Fin n)) (Iio t \ {i}) := by
          simp [disjoint_singleton_left]
        conv_lhs => rw [hunion]
        rw [sum_union hdisj, sum_singleton]
      _ = ∑ i ∈ Iio t, g i i + ∑ i ∈ Iio t, ∑ j ∈ Iio t \ {i}, g i j :=
        sum_add_distrib
  have hupper_lower :
    ∑ i ∈ Iio t, ∑ j ∈ Iio t \ {i}, g i j =
      ∑ i ∈ Iio t, ∑ j ∈ Ioo i t, g i j +
        ∑ i ∈ Iio t, ∑ j ∈ Iio i, g i j := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i hi => ?_
    have hpartition : Iio t \ {i} = Ioo i t ∪ Iio i := by
      ext j
      simp only [mem_sdiff, mem_Iio, mem_singleton, mem_union, mem_Ioo]
      constructor
      ·
        intro ⟨hjt, hne⟩
        exact (lt_or_gt_of_ne hne).elim (fun h => Or.inr h)
          fun h => Or.inl ⟨h, hjt⟩
      ·
        rintro (⟨hij, hjt⟩ | hji)
        · exact ⟨hjt, ne_of_gt hij⟩
        · exact ⟨lt_trans hji (mem_Iio.mp hi), ne_of_lt hji⟩
    have hdisj : Disjoint (Ioo i t) (Iio i) :=
      disjoint_left.mpr fun j hj hj' =>
        lt_asymm (mem_Ioo.mp hj).1 (mem_Iio.mp hj')
    rw [hpartition, sum_union hdisj]
  have hswap :
    ∑ i ∈ Iio t, ∑ j ∈ Iio i, g i j =
      star (∑ i ∈ Iio t, ∑ j ∈ Ioo i t, g i j) := calc
      _ = ∑ i ∈ Iio t, ∑ j ∈ Iio t, if j < i then g i j else 0 := by
        refine sum_congr rfl fun i hi => ?_
        have hset : (Iio t).filter (fun j => j < i) = Iio i := by
          ext j
          simp only [mem_filter, mem_Iio]
          exact ⟨And.right, fun hji => ⟨lt_trans hji (mem_Iio.mp hi), hji⟩⟩
        rw [← sum_filter, hset]
      _ = ∑ j ∈ Iio t, ∑ i ∈ Iio t, if j < i then g i j else 0 := sum_comm
      _ = ∑ j ∈ Iio t, ∑ i ∈ Ioo j t, g i j := by
        refine sum_congr rfl fun j _ => ?_
        have hset : (Iio t).filter (fun i => j < i) = Ioo j t := by
          ext i
          simp only [mem_filter, mem_Iio, mem_Ioo]
          exact ⟨fun ⟨hit, hji⟩ => ⟨hji, hit⟩, fun ⟨hji, hit⟩ => ⟨hit, hji⟩⟩
        rw [← sum_filter, hset]
      _ = ∑ j ∈ Iio t, ∑ i ∈ Ioo j t, star (g j i) :=
        sum_congr rfl fun j _ => sum_congr rfl fun i _ => hherm _ _
      _ = star (∑ j ∈ Iio t, ∑ i ∈ Ioo j t, g j i) := by
        change ∑ j ∈ Iio t, ∑ i ∈ Ioo j t, (starRingEnd ℂ) (g j i) =
          (starRingEnd ℂ) (∑ j ∈ Iio t, ∑ i ∈ Ioo j t, g j i)
        simp_rw [map_sum (starRingEnd ℂ)]
      _ = star (∑ i ∈ Iio t, ∑ j ∈ Ioo i t, g i j) := rfl
  rw [hsplit, hupper_lower, hswap, map_add, choleskyGtC_re_add_star]
  simp_rw [map_sum RCLike.re]


private lemma choleskyGtC_sum_S_sq
  (L : Matrix (Fin n) (Fin n) ℂ) (t : Fin n) (ξ : Fin n → ℂ) :
  ∑ c ∈ Iio t, ‖choleskyGtC_S L t ξ c‖ ^ 2 =
    RCLike.re (∑ i ∈ Iic t, ∑ j ∈ Iic t, star (choleskyGtC_w t ξ i) * choleskyGtC_w t ξ j * choleskyGtC_ip L t i j) := by
  have hnorm :
    ∀ c, ‖choleskyGtC_S L t ξ c‖ ^ 2 = RCLike.re (star (choleskyGtC_S L t ξ c) * choleskyGtC_S L t ξ c) := by
    intro c
    rw [RCLike.star_def, RCLike.conj_mul]
    norm_cast
  have h1 :
    ∑ c ∈ Iio t, ‖choleskyGtC_S L t ξ c‖ ^ 2 =
      RCLike.re (∑ c ∈ Iio t, star (choleskyGtC_S L t ξ c) * choleskyGtC_S L t ξ c) := by
    simp_rw [hnorm, ← map_sum RCLike.re]
  rw [h1]
  have hexpand :
    ∑ c ∈ Iio t, star (choleskyGtC_S L t ξ c) * choleskyGtC_S L t ξ c =
      ∑ c ∈ Iio t, ∑ i ∈ Icc c t, ∑ j ∈ Icc c t,
        star (choleskyGtC_w t ξ i) * choleskyGtC_w t ξ j * (star (L i c) * L j c) := by
    refine sum_congr rfl fun c _ => ?_
    dsimp [choleskyGtC_S]
    change (starRingEnd ℂ) (∑ i ∈ Icc c t, choleskyGtC_w t ξ i * L i c) *
        ∑ i ∈ Icc c t, choleskyGtC_w t ξ i * L i c =
      ∑ i ∈ Icc c t, ∑ j ∈ Icc c t,
        (starRingEnd ℂ) (choleskyGtC_w t ξ i) * choleskyGtC_w t ξ j * ((starRingEnd ℂ) (L i c) * L j c)
    rw [map_sum (starRingEnd ℂ), sum_mul_sum]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [map_mul (starRingEnd ℂ)]
    ring
  rw [hexpand]
  have h2 :
    ∀ c ∈ Iio t,
      ∑ i ∈ Icc c t, ∑ j ∈ Icc c t,
          star (choleskyGtC_w t ξ i) * choleskyGtC_w t ξ j * (star (L i c) * L j c) =
        ∑ i ∈ Iic t, ∑ j ∈ Iic t,
          if c ≤ i ∧ c ≤ j then
            star (choleskyGtC_w t ξ i) * choleskyGtC_w t ξ j * (star (L i c) * L j c)
          else 0 := by
    intro c hc
    have hct : c ≤ t := (mem_Iio.mp hc).le
    have hI : (Iic t).filter (fun i => c ≤ i) = Icc c t := choleskyGtC_filter_Iic_eq_Icc t hct
    calc
      _ = ∑ i ∈ (Iic t).filter (fun i => c ≤ i),
          ∑ j ∈ (Iic t).filter (fun j => c ≤ j),
            star (choleskyGtC_w t ξ i) * choleskyGtC_w t ξ j * (star (L i c) * L j c) := by rw [hI]
      _ = ∑ i ∈ Iic t, if c ≤ i then
          ∑ j ∈ Iic t, if c ≤ j then
            star (choleskyGtC_w t ξ i) * choleskyGtC_w t ξ j * (star (L i c) * L j c) else 0 else 0 := by
        simp_rw [sum_filter]
      _ = ∑ i ∈ Iic t, ∑ j ∈ Iic t,
          if c ≤ i ∧ c ≤ j then
            star (choleskyGtC_w t ξ i) * choleskyGtC_w t ξ j * (star (L i c) * L j c) else 0 := by
        refine sum_congr rfl fun i _ => ?_
        if hi : c ≤ i then
          simp [hi]
        else
          simp [hi]
  have hcomm :
    (∑ c ∈ Iio t, ∑ i ∈ Icc c t, ∑ j ∈ Icc c t,
        star (choleskyGtC_w t ξ i) * choleskyGtC_w t ξ j * (star (L i c) * L j c)) =
      (∑ i ∈ Iic t, ∑ j ∈ Iic t, ∑ c ∈ Iio t,
        if c ≤ i ∧ c ≤ j then
          star (choleskyGtC_w t ξ i) * choleskyGtC_w t ξ j * (star (L i c) * L j c) else 0) := by
    rw [sum_congr rfl h2, sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_comm]
  rw [hcomm]
  have hfilter :
    (∑ i ∈ Iic t, ∑ j ∈ Iic t, ∑ c ∈ Iio t,
        if c ≤ i ∧ c ≤ j then
          star (choleskyGtC_w t ξ i) * choleskyGtC_w t ξ j * (star (L i c) * L j c) else 0) =
      (∑ i ∈ Iic t, ∑ j ∈ Iic t,
        ∑ c ∈ (Iio t).filter (fun c => c ≤ i ∧ c ≤ j),
          star (choleskyGtC_w t ξ i) * choleskyGtC_w t ξ j * (star (L i c) * L j c)) := by
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    simp_rw [sum_filter]
  rw [hfilter]
  apply congr_arg RCLike.re
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  have hmin : (Iio t).filter (fun c => c ≤ i ∧ c ≤ j) =
    (Iio t).filter (fun c => c ≤ min i j) := by
    ext c; simp only [mem_filter, le_min_iff]
  unfold choleskyGtC_ip
  rw [hmin, mul_sum]


private lemma choleskyGtC_gram_eq_Qsum_add
  (L : Matrix (Fin n) (Fin n) ℂ) (t : Fin n) (ξ : Fin n → ℂ) :
  RCLike.re (∑ i ∈ Iic t, ∑ j ∈ Iic t, star (choleskyGtC_w t ξ i) * choleskyGtC_w t ξ j * choleskyGtC_ip L t i j) =
    choleskyGtC_Qsum L t ξ + ∑ c ∈ Iio t, ‖L t c‖ ^ 2 := by
  set s := Iio t
  have ht : t ∉ s := by
    dsimp [s]
    simp [mem_Iio]
  have hw_t : choleskyGtC_w t ξ t = 1 := by simp [choleskyGtC_w]
  have hw_s : ∀ i ∈ s, choleskyGtC_w t ξ i = ξ i := by
    intro i hi
    simp [choleskyGtC_w, ne_of_lt (mem_Iio.mp hi)]
  rw [choleskyGtC_Iic_eq_insert_Iio]
  set f : Fin n → Fin n → ℂ := fun i j => star (choleskyGtC_w t ξ i) * choleskyGtC_w t ξ j * choleskyGtC_ip L t i j
  change RCLike.re (∑ i ∈ insert t s, ∑ j ∈ insert t s, f i j) =
    choleskyGtC_Qsum L t ξ + ∑ c ∈ Iio t, ‖L t c‖ ^ 2
  rw [sum_insert ht, sum_insert ht]
  have hrest :
    ∑ i ∈ s, ∑ j ∈ insert t s, f i j =
      ∑ i ∈ s, f i t + ∑ i ∈ s, ∑ j ∈ s, f i j := by
    simp_rw [sum_insert ht, sum_add_distrib]
  rw [hrest, ← add_assoc]
  have hshape :
    f t t + ∑ j ∈ s, f t j + ∑ i ∈ s, f i t +
        ∑ i ∈ s, ∑ j ∈ s, f i j =
      f t t + (∑ j ∈ s, f t j + ∑ i ∈ s, f i t) +
        ∑ i ∈ s, ∑ j ∈ s, f i j := by
    abel
  rw [hshape]
  have hftt : f t t = choleskyGtC_ip L t t t := by
    dsimp [f]; rw [hw_t]; simp
  have hftj' : ∑ j ∈ s, f t j = ∑ j ∈ s, ξ j * choleskyGtC_ip L t t j := by
    refine sum_congr rfl fun j hj => ?_
    dsimp [f]; rw [hw_t, hw_s j hj]; simp
  have hfit' : ∑ i ∈ s, f i t = ∑ i ∈ s, star (ξ i) * choleskyGtC_ip L t i t := by
    refine sum_congr rfl fun i hi => ?_
    dsimp [f]; rw [hw_t, hw_s i hi]; simp
  have hfij' :
    ∑ i ∈ s, ∑ j ∈ s, f i j =
      ∑ i ∈ s, ∑ j ∈ s, star (ξ i) * ξ j * choleskyGtC_ip L t i j := by
    refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
    dsimp [f]; rw [hw_s i hi, hw_s j hj]
  rw [hftt, hftj', hfit', hfij']
  have hcross_re :
    RCLike.re
      (∑ j ∈ s, ξ j * choleskyGtC_ip L t t j + ∑ i ∈ s, star (ξ i) * choleskyGtC_ip L t i t) =
      2 * RCLike.re (∑ i ∈ s, star (ξ i) * choleskyGtC_ip L t i t) := by
    have hstar :
      ∑ j ∈ s, ξ j * choleskyGtC_ip L t t j =
        star (∑ i ∈ s, star (ξ i) * choleskyGtC_ip L t i t) := by
      refine Eq.trans ?_ (Eq.symm (map_sum (starRingEnd ℂ)
        (fun i => star (ξ i) * choleskyGtC_ip L t i t) s))
      refine sum_congr rfl fun j _ => ?_
      rw [choleskyGtC_ip_star, RCLike.star_def, map_mul (starRingEnd ℂ), starRingEnd_self_apply]
      try ring
    rw [hstar, add_comm, choleskyGtC_re_add_star]
  have hbilin :
    RCLike.re (∑ i ∈ s, ∑ j ∈ s, star (ξ i) * ξ j * choleskyGtC_ip L t i j) =
      ∑ i ∈ s, ‖ξ i‖ ^ 2 * ∑ k ∈ Iic i, ‖L i k‖ ^ 2 +
        2 * ∑ i ∈ s, ∑ j ∈ Ioo i t,
          RCLike.re (star (ξ i) * ξ j * choleskyGtC_ip L t i j) := by
    let g : Fin n → Fin n → ℂ := fun i j => star (ξ i) * ξ j * choleskyGtC_ip L t i j
    have hherm : ∀ i j, g j i = star (g i j) := by
      intro i j
      dsimp [g]
      rw [choleskyGtC_ip_star]
      change star (ξ j) * ξ i * star (choleskyGtC_ip L t i j) =
        star (star (ξ i) * ξ j * choleskyGtC_ip L t i j)
      rw [RCLike.star_def, map_mul (starRingEnd ℂ), map_mul (starRingEnd ℂ),
        starRingEnd_self_apply]
      ring
    have h := choleskyGtC_sum_sum_herm (t := t) (g := g) hherm
    have hdiag :
      ∑ i ∈ s, RCLike.re (g i i) =
        ∑ i ∈ s, ‖ξ i‖ ^ 2 * ∑ k ∈ Iic i, ‖L i k‖ ^ 2 := by
      refine sum_congr rfl fun i hi => ?_
      dsimp [g]
      have hi' : i < t := mem_Iio.mp hi
      rw [choleskyGtC_ip_diag_of_lt L hi']
      have hxi : (starRingEnd ℂ) (ξ i) * ξ i = ((‖ξ i‖ ^ 2 : ℝ) : ℂ) := by
        rw [RCLike.conj_mul]; norm_cast
      change RCLike.re ((starRingEnd ℂ) (ξ i) * ξ i * ((∑ k ∈ Iic i, ‖L i k‖ ^ 2 : ℝ) : ℂ)) = _
      rw [hxi, ← Complex.ofReal_mul]
      exact RCLike.ofReal_re _
    simp only [s] at h hdiag ⊢
    rw [h, hdiag]
  have hsplit :
    ∀ i ∈ Iio t,
      ∑ j ∈ Ioc i t, choleskyGtC_w t ξ j * ∑ k ∈ Iic i, star (L i k) * L j k =
        ∑ j ∈ Ioo i t, ξ j * choleskyGtC_ip L t i j + choleskyGtC_ip L t i t := by
    intro i hi
    have hit : i < t := mem_Iio.mp hi
    have hIoc : Ioc i t = insert t (Ioo i t) := by
      ext j
      simp only [mem_Ioc, mem_insert, mem_Ioo]
      constructor
      ·
        intro ⟨hij, hjt⟩
        exact (lt_or_eq_of_le hjt).elim (fun h => Or.inr ⟨hij, h⟩) Or.inl
      ·
        rintro (rfl | ⟨hij, hjt⟩)
        · exact ⟨hit, le_rfl⟩
        · exact ⟨hij, hjt.le⟩
    rw [hIoc, sum_insert (by simp [mem_Ioo])]
    simp only [hw_t]
    have ht_term : ∑ k ∈ Iic i, star (L i k) * L t k = choleskyGtC_ip L t i t :=
      (choleskyGtC_ip_of_le_of_lt L (le_of_lt hit) hit).symm
    have hj_term :
      ∑ j ∈ Ioo i t, choleskyGtC_w t ξ j * ∑ k ∈ Iic i, star (L i k) * L j k =
        ∑ j ∈ Ioo i t, ξ j * choleskyGtC_ip L t i j := by
      refine sum_congr rfl fun j hj => ?_
      have hjt : j < t := (mem_Ioo.mp hj).2
      have hij : i < j := (mem_Ioo.mp hj).1
      simp only [choleskyGtC_w, ne_of_lt hjt, ite_false]
      rw [choleskyGtC_ip_of_le_of_lt L hij.le hit]
    rw [hj_term, ht_term, one_mul, add_comm]
  have hQ :
    choleskyGtC_Qsum L t ξ =
      ∑ i ∈ s, ‖ξ i‖ ^ 2 * ∑ k ∈ Iic i, ‖L i k‖ ^ 2 +
        2 * ∑ i ∈ s, ∑ j ∈ Ioo i t,
          RCLike.re (star (ξ i) * ξ j * choleskyGtC_ip L t i j) +
        2 * RCLike.re (∑ i ∈ s, star (ξ i) * choleskyGtC_ip L t i t) := by
    -- Force `RCLike.re` (not `Complex.re`) in the unfolded choleskyGtC_Qsum.
    change (∑ i ∈ Iio t,
        (‖ξ i‖ ^ 2 * ∑ k ∈ Iic i, ‖L i k‖ ^ 2 +
          2 * RCLike.re (star (ξ i) *
            ∑ j ∈ Ioc i t, choleskyGtC_w t ξ j * ∑ k ∈ Iic i, star (L i k) * L j k))) =
      ∑ i ∈ s, ‖ξ i‖ ^ 2 * ∑ k ∈ Iic i, ‖L i k‖ ^ 2 +
        2 * ∑ i ∈ s, ∑ j ∈ Ioo i t,
          RCLike.re (star (ξ i) * ξ j * choleskyGtC_ip L t i j) +
        2 * RCLike.re (∑ i ∈ s, star (ξ i) * choleskyGtC_ip L t i t)
    have hterm :
      ∀ i ∈ Iio t,
        ‖ξ i‖ ^ 2 * ∑ k ∈ Iic i, ‖L i k‖ ^ 2 +
            2 * RCLike.re
              (star (ξ i) *
                ∑ j ∈ Ioc i t, choleskyGtC_w t ξ j *
                  ∑ k ∈ Iic i, star (L i k) * L j k) =
          ‖ξ i‖ ^ 2 * ∑ k ∈ Iic i, ‖L i k‖ ^ 2 +
            2 * ∑ j ∈ Ioo i t,
              RCLike.re (star (ξ i) * ξ j * choleskyGtC_ip L t i j) +
            2 * RCLike.re (star (ξ i) * choleskyGtC_ip L t i t) := by
      intro i hi
      rw [hsplit i hi, mul_add, map_add RCLike.re]
      have hrearr :
        RCLike.re (star (ξ i) * ∑ j ∈ Ioo i t, ξ j * choleskyGtC_ip L t i j) =
          ∑ j ∈ Ioo i t, RCLike.re (star (ξ i) * ξ j * choleskyGtC_ip L t i j) := by
        rw [mul_sum, map_sum RCLike.re]
        refine sum_congr rfl fun j _ => by ring_nf
      rw [hrearr]
      ring
    rw [sum_congr rfl hterm]
    simp_rw [sum_add_distrib]
    have h2re :
      (∑ i ∈ Iio t, 2 * RCLike.re (star (ξ i) * choleskyGtC_ip L t i t)) =
        2 * RCLike.re (∑ i ∈ Iio t, star (ξ i) * choleskyGtC_ip L t i t) := by
      rw [← mul_sum, map_sum RCLike.re]
    have h2upper :
      (∑ i ∈ Iio t,
          2 * ∑ j ∈ Ioo i t, RCLike.re (star (ξ i) * ξ j * choleskyGtC_ip L t i j)) =
        2 * ∑ i ∈ Iio t, ∑ j ∈ Ioo i t,
          RCLike.re (star (ξ i) * ξ j * choleskyGtC_ip L t i j) := by
      simp_rw [← mul_sum]
    rw [h2re, h2upper]

  have htt_re : RCLike.re (choleskyGtC_ip L t t t) = ∑ c ∈ Iio t, ‖L t c‖ ^ 2 := by
    rw [choleskyGtC_ip_tt]; exact RCLike.ofReal_re _
  rw [map_add, map_add, htt_re, hcross_re, hbilin, hQ]
  ring

private lemma choleskyGtC_Qsum_eq
  (L : Matrix (Fin n) (Fin n) ℂ) (t : Fin n) (ξ : Fin n → ℂ) :
  choleskyGtC_Qsum L t ξ =
    (∑ c ∈ Iio t, ‖choleskyGtC_S L t ξ c‖ ^ 2) - ∑ c ∈ Iio t, ‖L t c‖ ^ 2 := by
  linarith [choleskyGtC_gram_eq_Qsum_add L t ξ, choleskyGtC_sum_S_sq L t ξ]


@[path]
private lemma main
  {n : ℕ}
  {t : Fin n}
  {A L : Matrix (Fin n) (Fin n) ℂ}
-- given
  (h₀ : ∀ i, i < t → 0 < L i i)
  (h₁ : ∀ ξ : Fin n → ℂ,
    0 < A t t + ((∑ i ∈ Finset.Iio t,
      (‖ξ i‖ ^ 2 * ∑ k ∈ Finset.Iic i, ‖L i k‖ ^ 2 +
        2 * RCLike.re (star (ξ i) *
          ∑ j ∈ Finset.Ioc i t,
            (if j = t then (1 : ℂ) else ξ j) *
              ∑ k ∈ Finset.Iic i, star (L i k) * L j k)) : ℝ) : ℂ)) :
-- imply
  ((∑ k ∈ Finset.Iio t, ‖L t k‖ ^ 2 : ℝ) : ℂ) < A t t := by
-- proof
  have hS0 : ∀ c ∈ Iio t, choleskyGtC_S L t (choleskyGtC_optξ L t) c = 0 := fun c hc =>
    choleskyGtC_S_optξ_eq_zero L t h₀ hc
  have hQ := choleskyGtC_Qsum_eq L t (choleskyGtC_optξ L t)
  have h1 := h₁ (choleskyGtC_optξ L t)
  have hQ0 : choleskyGtC_Qsum L t (choleskyGtC_optξ L t) = -∑ c ∈ Iio t, ‖L t c‖ ^ 2 := by
    rw [hQ]
    have : ∑ c ∈ Iio t, ‖choleskyGtC_S L t (choleskyGtC_optξ L t) c‖ ^ 2 = 0 :=
      sum_eq_zero fun c hc => by simp [hS0 c hc]
    rw [this, zero_sub]
  change 0 < A t t + (choleskyGtC_Qsum L t (choleskyGtC_optξ L t) : ℂ) at h1
  rw [hQ0] at h1
  have hsub :
    A t t + ((-∑ c ∈ Iio t, ‖L t c‖ ^ 2 : ℝ) : ℂ) =
      A t t - ((∑ c ∈ Iio t, ‖L t c‖ ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [hsub] at h1
  exact sub_pos.mp h1


@[path]
private lemma real
  {n : ℕ}
  {t : Fin n}
  {A L : Matrix (Fin n) (Fin n) ℝ}
-- given
  (h₀ : ∀ i, i < t → 0 < L i i)
  (h₁ : ∀ ξ : Fin n → ℝ,
    0 < A t t + ∑ i ∈ Finset.Iio t,
      (ξ i ^ 2 * ∑ k ∈ Finset.Iic i, L i k ^ 2 +
        2 * ξ i * ∑ j ∈ Finset.Ioc i t,
          (if j = t then (1 : ℝ) else ξ j) * ∑ k ∈ Finset.Iic i, L j k * L i k)) :
-- imply
  ∑ k ∈ Finset.Iio t, ‖L t k‖ ^ 2 < A t t := by
-- proof
  simp_rw [Real.norm_eq_abs, sq_abs]
  have hS0 : ∀ c ∈ Iio t, choleskyGt_S L t (choleskyGt_optξ L t) c = 0 := fun c hc =>
    choleskyGt_S_optξ_eq_zero L t h₀ hc
  have hQ := choleskyGt_Qsum_eq L t (choleskyGt_optξ L t)
  have h1 := h₁ (choleskyGt_optξ L t)
  have hQ0 : choleskyGt_Qsum L t (choleskyGt_optξ L t) = -∑ c ∈ Iio t, L t c ^ 2 := by
    rw [hQ]
    have : ∑ c ∈ Iio t, choleskyGt_S L t (choleskyGt_optξ L t) c ^ 2 = 0 :=
      sum_eq_zero fun c hc => by simp [hS0 c hc]
    rw [this, zero_sub]
  change 0 < A t t + choleskyGt_Qsum L t (choleskyGt_optξ L t) at h1
  rw [hQ0] at h1
  linarith


-- created on 2023-06-29
