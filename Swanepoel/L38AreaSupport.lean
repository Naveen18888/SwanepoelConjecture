module
public import Swanepoel.Lemma37
@[expose] public section

noncomputable section
namespace Swanepoel

def l38SupportBody (N : Set Plane) (r : ℝ) : Set Plane :=
  {q | ‖q‖ ≤ 1 ∧ ∀ n ∈ N, inner ℝ q n ≤ r}

theorem l38SupportBody_isClosed (N : Set Plane) (r : ℝ) : IsClosed (l38SupportBody N r) := by
  have heq : l38SupportBody N r = {q : Plane | ‖q‖ ≤ 1} ∩ ⋂ n ∈ N, {q : Plane | inner ℝ q n ≤ r} := by
    ext q
    simp only [l38SupportBody,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter]
  rw [heq]
  exact (isClosed_le continuous_norm continuous_const).inter
    (isClosed_iInter (fun n => isClosed_iInter (fun _ =>
      isClosed_le (continuous_id.inner continuous_const) continuous_const)))

theorem l38SupportBody_convex (N : Set Plane) (r : ℝ) : Convex ℝ (l38SupportBody N r) := by
  intro p hp q hq a b ha hb hab
  constructor
  · calc
      ‖a • p+b • q‖≤‖a • p‖+‖b • q‖ := norm_add_le _ _
      _ = a*‖p‖+b*‖q‖ := by rw [norm_smul,norm_smul,Real.norm_eq_abs,
          Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb]
      _ ≤ a+b := by
        simpa only [mul_one] using add_le_add
          (mul_le_mul_of_nonneg_left hp.1 ha) (mul_le_mul_of_nonneg_left hq.1 hb)
      _ = 1 := hab
  · intro n hn
    rw [inner_add_left,real_inner_smul_left,real_inner_smul_left]
    calc
      a*inner ℝ p n+b*inner ℝ q n ≤ a*r+b*r :=
        add_le_add (mul_le_mul_of_nonneg_left (hp.2 n hn) ha)
          (mul_le_mul_of_nonneg_left (hq.2 n hn) hb)
      _ = r := by rw [← add_mul,hab,one_mul]

theorem l38SupportBody_subset_closedBall (N : Set Plane) (r : ℝ) :
    l38SupportBody N r ⊆ Metric.closedBall 0 1 := by
  intro q hq
  simpa only [Metric.mem_closedBall,dist_zero_right] using hq.1

theorem l38SupportBody_isCompact (N : Set Plane) (r : ℝ) : IsCompact (l38SupportBody N r) :=
  Metric.isCompact_of_isClosed_isBounded (l38SupportBody_isClosed N r)
    (Metric.isBounded_closedBall.subset (l38SupportBody_subset_closedBall N r))

theorem zero_mem_l38SupportBody (N : Set Plane) {r : ℝ} (hr : 0 ≤ r) : (0:Plane) ∈ l38SupportBody N r := by
  constructor
  · norm_num
  · intro n _
    simpa only [inner_zero_left] using hr

theorem closedBall_subset_l38SupportBody (N : Set Plane) (hN : ∀ n∈N,‖n‖=1)
    {r : ℝ} (_hr0 : 0 ≤ r) (hr1 : r ≤ 1) : Metric.closedBall 0 r ⊆ l38SupportBody N r := by
  intro q hq
  have hnorm : ‖q‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_zero_right] using hq
  refine ⟨hnorm.trans hr1,?_⟩
  intro n hn
  have h := real_inner_le_norm q n
  rw [hN n hn,mul_one] at h
  exact h.trans hnorm

theorem l38SupportBody_bank_bound (N : Set Plane) {r : ℝ} {q n : Plane}
    (hq : q ∈ l38SupportBody N r) (hn : n ∈ N) : inner ℝ q n ≤ r := hq.2 n hn

theorem l38SupportBody_return_bound (N : Set Plane) {r : ℝ} {q n : Plane}
    (hq : q ∈ l38SupportBody N r) (hn : ‖n‖ = 1) : inner ℝ q n ≤ 1 := by
  have h := real_inner_le_norm q n
  rw [hn,mul_one] at h
  exact h.trans hq.1

theorem l38SupportBody_scaled_bank_bound (N : Set Plane) {r t : ℝ} {q n : Plane}
    (hq : q ∈ l38SupportBody N r) (hn : n ∈ N) (ht : 0 ≤ t) : inner ℝ (t • q) n ≤ t*r := by
  rw [real_inner_smul_left]
  exact mul_le_mul_of_nonneg_left (hq.2 n hn) ht

theorem l38SupportBody_scaled_return_bound (N : Set Plane) {r t : ℝ} {q n : Plane}
    (hq : q ∈ l38SupportBody N r) (hn : ‖n‖ = 1) (ht : 0 ≤ t) : inner ℝ (t • q) n ≤ t := by
  rw [real_inner_smul_left]
  exact (mul_le_mul_of_nonneg_left (l38SupportBody_return_bound N hq hn) ht).trans_eq (mul_one t)

theorem l38SupportBody_axis_extrema (N : Set Plane) (hN : ∀ n ∈ N, ‖n‖ = 1)
    (u : Plane) (hu : ‖u‖ = 1) (huN : u ∈ N) (hfront : ∀ n ∈ N, 0 ≤ inner ℝ u n)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    -u ∈ l38SupportBody N r ∧ r • u ∈ l38SupportBody N r ∧
      ∀ q ∈ l38SupportBody N r, -1 ≤ inner ℝ q u ∧ inner ℝ q u ≤ r := by
  refine ⟨⟨by simpa only [norm_neg,hu] using le_refl (1:ℝ),?_⟩,?_,?_⟩
  · intro n hn
    rw [inner_neg_left]
    linarith only [hfront n hn,hr0]
  · apply closedBall_subset_l38SupportBody N hN hr0 hr1
    rw [Metric.mem_closedBall,dist_zero_right,norm_smul,hu,Real.norm_eq_abs,abs_of_nonneg hr0,mul_one]
  · intro q hq
    have habs := abs_real_inner_le_norm q u
    rw [hu,mul_one] at habs
    exact ⟨(abs_le.mp (habs.trans hq.1)).1,hq.2 u huN⟩

def l38BankArc (u : Plane) : Set Plane := {n | ‖n‖ = 1 ∧ Real.sqrt 3/2 ≤ inner ℝ u n}

theorem axis_mem_l38BankArc (u : Plane) (hu : ‖u‖=1) : u∈l38BankArc u := by
  refine ⟨hu,?_⟩
  rw [real_inner_self_eq_norm_sq,hu]
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have hn := Real.sqrt_nonneg (3:ℝ)
  nlinarith only [hs,hn]

theorem l38_bank_support_extrema (u : Plane) (hu : ‖u‖=1) :
    -u∈l38SupportBody (l38BankArc u) (1/3) ∧
    (1/3:ℝ) • u∈l38SupportBody (l38BankArc u) (1/3) ∧
    ∀ q ∈ l38SupportBody (l38BankArc u) (1/3), -1 ≤ inner ℝ q u ∧ inner ℝ q u ≤ 1/3 := by
  apply l38SupportBody_axis_extrema (l38BankArc u) (fun _ hn => hn.1) u hu
    (axis_mem_l38BankArc u hu) ?_ (by norm_num) (by norm_num)
  intro n hn
  have hs := Real.sqrt_nonneg (3:ℝ)
  linarith only [hn.2,hs]

theorem printed_l38_support_excludes_zero (N : Set Plane) (hN : N.Nonempty)
    {r : ℝ} (hr : 0 < r) : (0:Plane) ∉ {q | ∀ n ∈ N, r ≤ inner ℝ q n} := by
  intro h
  obtain ⟨n,hn⟩ := hN
  have hh := h n hn
  rw [inner_zero_left] at hh
  exact (not_le_of_gt hr) hh

end Swanepoel
