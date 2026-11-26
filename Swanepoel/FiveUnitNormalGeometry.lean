module
public import Swanepoel.UnitConeProjection
public import Swanepoel.PentagonConvexity
@[expose] public section

noncomputable section
namespace Swanepoel

private theorem fung_cross_swap (x y : Plane) : cross2 x y= -cross2 y x := by
  unfold cross2
  ring

theorem unit_three_chain_extremes_cross_neg (a t b : Plane)
    (ha : ‖a‖=1) (ht : ‖t‖=1) (hb : ‖b‖=1)
    (hat : (-1/2:ℝ) < inner ℝ a t) (htb : (-1/2:ℝ) < inner ℝ t b)
    (hab : (-1/2:ℝ) < inner ℝ a b) (hcat : cross2 a t<0) (hctb : cross2 t b<0) :
    cross2 a b<0 := by
  let z := a+t+b
  have hcommTA : inner ℝ t a=inner ℝ a t := real_inner_comm _ _
  have hcommBA : inner ℝ b a=inner ℝ a b := real_inner_comm _ _
  have hcommBT : inner ℝ b t=inner ℝ t b := real_inner_comm _ _
  have hza : 0 < inner ℝ z a := by
    simp only [z,inner_add_left,real_inner_self_eq_norm_sq,ha,hcommTA,hcommBA]
    nlinarith
  have hzt : 0 < inner ℝ z t := by
    simp only [z,inner_add_left,real_inner_self_eq_norm_sq,ht,hcommBT]
    nlinarith
  have hzb : 0 < inner ℝ z b := by
    simp only [z,inner_add_left,real_inner_self_eq_norm_sq,hb]
    nlinarith
  have hid : inner ℝ z t*cross2 a b=
      inner ℝ z a*cross2 t b+inner ℝ z b*cross2 a t := by
    simp [cross2,PiLp.inner_apply,Fin.sum_univ_two]
    ring
  have hneg := add_neg (mul_neg_of_pos_of_neg hza hctb) (mul_neg_of_pos_of_neg hzb hcat)
  rw [← hid] at hneg
  exact (mul_neg_iff.mp hneg).resolve_right (fun h => hzt.not_gt h.1) |>.2

theorem five_unit_chain_two_step_inner_le (a t b u v : Plane)
    (ha : ‖a‖=1) (ht : ‖t‖=1) (hb : ‖b‖=1) (hu : ‖u‖=1) (hv : ‖v‖=1)
    (hbalance : a+b+t=u+v)
    (hat : (-1/2:ℝ) < inner ℝ a t) (htb : (-1/2:ℝ) < inner ℝ t b)
    (hau : inner ℝ a u<1/2) (hbv : inner ℝ b v<1/2)
    (hcat : cross2 a t<0) (hctb : cross2 t b<0)
    (hcau : cross2 a u<0) (hcbv : 0<cross2 b v) :
    inner ℝ a b≤ -1/2 := by
  by_contra hn
  have hab : (-1/2:ℝ) < inner ℝ a b := lt_of_not_ge hn
  have hcross := unit_three_chain_extremes_cross_neg a t b ha ht hb hat htb hab hcat hctb
  let c := ‖a+b‖
  have hc : 1<c := by
    have h := norm_add_sq_real a b
    rw [ha,hb] at h
    have hnonneg := norm_nonneg (a+b)
    change 1<‖a+b‖
    nlinarith [sq_nonneg (‖a+b‖-1)]
  have hc0 : 0<c := by linarith
  let e := NormedSpace.normalize (a+b)
  have he : ‖e‖=1 := NormedSpace.norm_normalize (norm_pos_iff.mp hc0)
  have hsum : c • e=a+b := NormedSpace.norm_smul_normalize _
  have habcomm : inner ℝ b a=inner ℝ a b := real_inner_comm _ _
  have hca : inner ℝ e a=c/2 := by
    have h := congrArg (fun z : Plane => inner ℝ z a) hsum
    simp only [real_inner_smul_left,inner_add_left,real_inner_self_eq_norm_sq,ha,habcomm] at h
    have hs := norm_add_sq_real a b
    rw [ha,hb] at hs
    change c^2=_ at hs
    have hz : c*(inner ℝ e a-c/2)=0 := by nlinarith only [h,hs]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (ne_of_gt hc0))
  have hcb : inner ℝ e b=c/2 := by
    have h := congrArg (fun z : Plane => inner ℝ z b) hsum
    simp only [real_inner_smul_left,inner_add_left,real_inner_self_eq_norm_sq,hb] at h
    have hs := norm_add_sq_real a b
    rw [ha,hb] at hs
    change c^2=_ at hs
    have hz : c*(inner ℝ e b-c/2)=0 := by nlinarith only [h,hs]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (ne_of_gt hc0))
  have hcea : 0<cross2 e a := by
    have h := congrArg (fun z : Plane => cross2 z a) hsum
    rw [cross2_smul_left,cross2_add_left,cross2_self,fung_cross_swap b a] at h
    have hp : 0<c*cross2 e a := by nlinarith only [h,hcross]
    exact (mul_pos_iff.mp hp).resolve_right (fun h => hc0.not_gt h.1) |>.2
  have hceb : cross2 e b<0 := by
    have h := congrArg (fun z : Plane => cross2 z b) hsum
    rw [cross2_smul_left,cross2_add_left,cross2_self] at h
    have hp : c*cross2 e b<0 := by nlinarith only [h,hcross]
    exact (mul_neg_iff.mp hp).resolve_right (fun h => hc0.not_gt h.1) |>.2
  have hcone : ∃ r s : ℝ,0<r ∧ 0<s ∧ t=r • a+s • b := by
    refine ⟨cross2 t b/cross2 a b,cross2 a t/cross2 a b,
      div_pos_of_neg_of_neg hctb hcross,div_pos_of_neg_of_neg hcat hcross,
      (cramer_reconstruct a b t (ne_of_lt hcross)).symm⟩
  obtain ⟨r,s,hr,hs,hrepr⟩ := hcone
  have het : 0 < inner ℝ e t := by
    rw [hrepr,inner_add_right,real_inner_smul_right,real_inner_smul_right,hca,hcb]
    positivity
  have hprojection : 1 < inner ℝ e (u+v) := by
    rw [← hbalance,inner_add_right,inner_add_right,hca,hcb]
    linarith
  have hubound := real_inner_le_norm e u
  have hvbound := real_inner_le_norm e v
  rw [he,hu,mul_one] at hubound
  rw [he,hv,mul_one] at hvbound
  rw [inner_add_right] at hprojection
  have heu : 0 < inner ℝ e u := by linarith
  have hev : 0 < inner ℝ e v := by linarith
  have hcu := unit_gap_below_axis e a u he ha hu (by rw [hca]; linarith) hcea hcau hau
  have hcv := unit_gap_above_axis e b v he hb hv (by rw [hcb]; linarith) hceb hcbv hbv
  have hnear := unit_straddling_sum_sub_axis_lt_one e u v he hu hv heu hev hcu hcv
  have hnorm : ‖e-(u+v)‖^2=(c-1)^2+1+2*(c-1)*inner ℝ e t := by
    rw [← hbalance,← hsum]
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left,inner_sub_right,inner_add_left,
      inner_add_right,real_inner_smul_left,real_inner_smul_right,
      show inner ℝ t e=inner ℝ e t from real_inner_comm _ _,
      real_inner_self_eq_norm_sq,he,ht]
    rw [norm_smul,he,Real.norm_eq_abs,abs_of_pos hc0,mul_one]
    ring
  have hfar : 1<‖e-(u+v)‖^2 := by
    have hp := mul_pos (show 0<c-1 by linarith) het
    nlinarith only [hnorm,hp,sq_nonneg (c-1)]
  have hn0 := norm_nonneg (e-(u+v))
  have hsmall := (sq_lt_sq₀ hn0 (by norm_num : (0:ℝ)≤1)).mpr hnear
  norm_num only [one_pow] at hsmall
  linarith only [hsmall,hfar]

end Swanepoel
