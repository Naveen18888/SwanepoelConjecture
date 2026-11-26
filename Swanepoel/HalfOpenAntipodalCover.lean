module
public import Swanepoel.PentagonConeCount
@[expose] public section

noncomputable section
namespace Swanepoel

theorem unit_closed_projection_boundary (a b x : Plane)
    (ha : ‖a‖=1) (hb : ‖b‖=1) (hx : ‖x‖=1)
    (hab : |inner ℝ a b|≤1/2) (hax : |inner ℝ a x|≤1/2) (hbx : |inner ℝ b x|≤1/2) :
    (inner ℝ a x)^2=1/4 ∧ (inner ℝ b x)^2=1/4 := by
  have hsq (t : ℝ) (h : |t|≤1/2) : t^2≤1/4 := by
    have hh := (sq_le_sq₀ (abs_nonneg t) (by norm_num : (0:ℝ)≤1/2)).mpr h
    nlinarith only [hh,sq_abs t]
  have habx : |inner ℝ a b| * |inner ℝ b x|≤(1/4:ℝ) := by
    have h := mul_le_mul hab hbx (abs_nonneg _) (by norm_num : (0:ℝ)≤1/2)
    nlinarith only [h]
  have hp : |inner ℝ a b*inner ℝ b x*inner ℝ a x|≤(1/8:ℝ) := by
    rw [abs_mul,abs_mul]
    have h := mul_le_mul habx hax (abs_nonneg _) (by norm_num : (0:ℝ)≤1/4)
    nlinarith only [h]
  have hg := plane_gram_identity a b x
  have hcomm : inner ℝ x a=inner ℝ a x := real_inner_comm _ _
  rw [ha,hb,hx,hcomm] at hg
  constructor <;> nlinarith only [hg,(abs_le.mp hp).1,hsq _ hab,hsq _ hax,hsq _ hbx]

theorem HalfOpen120Cone.abs_projection_le_of_missing {a x : Plane}
    (hn : ¬HalfOpen120Cone a x) (hm : ¬HalfOpen120Cone a (-x)) : |inner ℝ a x|≤1/2 := by
  rw [abs_le]
  constructor
  · by_contra h
    apply hm
    left
    rw [inner_neg_right]
    linarith only [h]
  · by_contra h
    exact hn (Or.inl (lt_of_not_ge h))

theorem HalfOpen120Cone.missing_boundary_product_neg {a x : Plane}
    (ha : ‖a‖=1) (hx : ‖x‖=1) (hsq : (inner ℝ a x)^2=1/4)
    (hn : ¬HalfOpen120Cone a x) (hm : ¬HalfOpen120Cone a (-x)) :
    inner ℝ a x*cross2 a x<0 := by
  have hg := cross2_sq_add_inner_sq a x
  rw [ha,hx,hsq] at hg
  have hcne : cross2 a x≠0 := by intro h; rw [h] at hg; norm_num at hg
  have hfactor : (inner ℝ a x-1/2)*(inner ℝ a x+1/2)=0 := by nlinarith only [hsq]
  rcases mul_eq_zero.mp hfactor with h | h
  · have heq : inner ℝ a x=1/2 := by linarith only [h]
    have hc : cross2 a x≤0 := le_of_not_gt (fun hp => hn (Or.inr ⟨heq,hp⟩))
    rw [heq]
    exact mul_neg_of_pos_of_neg (by norm_num) (lt_of_le_of_ne hc hcne)
  · have heq : inner ℝ a x= -1/2 := by linarith only [h]
    have hcross : cross2 a (-x)= -cross2 a x := by simp [cross2]; ring
    have hc : 0≤cross2 a x := by
      by_contra hh
      apply hm
      right
      constructor
      · rw [inner_neg_right,heq]; ring
      · rw [hcross]; linarith only [hh]
    rw [heq]
    exact mul_neg_of_neg_of_pos (by norm_num) (lt_of_le_of_ne hc (Ne.symm hcne))

theorem half_open_two_cones_antipodal_cover (a b x : Plane)
    (ha : ‖a‖=1) (hb : ‖b‖=1) (hx : ‖x‖=1) (hab : |inner ℝ a b|≤1/2) :
    HalfOpen120Cone a x ∨ HalfOpen120Cone b x ∨
      HalfOpen120Cone a (-x) ∨ HalfOpen120Cone b (-x) := by
  by_contra hn
  push Not at hn
  have hax := HalfOpen120Cone.abs_projection_le_of_missing hn.1 hn.2.2.1
  have hbx := HalfOpen120Cone.abs_projection_le_of_missing hn.2.1 hn.2.2.2
  obtain ⟨haxs,hbxs⟩ := unit_closed_projection_boundary a b x ha hb hx hab hax hbx
  have hpa := HalfOpen120Cone.missing_boundary_product_neg ha hx haxs hn.1 hn.2.2.1
  have hpb := HalfOpen120Cone.missing_boundary_product_neg hb hx hbxs hn.2.1 hn.2.2.2
  have hproduct := mul_pos_of_neg_of_neg hpa hpb
  have hga := cross2_sq_add_inner_sq a x
  have hgb := cross2_sq_add_inner_sq b x
  rw [ha,hx,haxs] at hga
  rw [hb,hx,hbxs] at hgb
  have hcas : (cross2 a x)^2=3/4 := by nlinarith only [hga]
  have hcbs : (cross2 b x)^2=3/4 := by nlinarith only [hgb]
  have hdot : inner ℝ a b=inner ℝ a x*inner ℝ b x+cross2 a x*cross2 b x := by
    have h := inner_cross_identity x a b
    have hxa : inner ℝ x a=inner ℝ a x := real_inner_comm _ _
    have hxb : inner ℝ x b=inner ℝ b x := real_inner_comm _ _
    have hcxa : cross2 x a= -cross2 a x := by unfold cross2; ring
    have hcxb : cross2 x b= -cross2 b x := by unfold cross2; ring
    rw [hx,hxa,hxb,hcxa,hcxb] at h
    nlinarith only [h]
  have hproj : (inner ℝ a x*inner ℝ b x)^2=1/16 := by rw [mul_pow,haxs,hbxs]; norm_num
  have hcross : (cross2 a x*cross2 b x)^2=9/16 := by rw [mul_pow,hcas,hcbs]; norm_num
  have hfull : (inner ℝ a b)^2=(inner ℝ a x*inner ℝ b x)^2+(cross2 a x*cross2 b x)^2+
      2*(inner ℝ a x*cross2 a x)*(inner ℝ b x*cross2 b x) := by rw [hdot]; ring
  have hbound : (inner ℝ a b)^2≤1/4 := by
    have hh := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mpr hab
    nlinarith only [hh,sq_abs (inner ℝ a b)]
  nlinarith only [hfull,hproj,hcross,hproduct,hbound]

end Swanepoel
