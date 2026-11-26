module
public import Swanepoel.UnitCapGeometry
public import Swanepoel.FaceBoundaryOrder
@[expose] public section

noncomputable section
namespace Swanepoel

private theorem ucp_cross_swap (x y : Plane) : cross2 x y= -cross2 y x := by
  unfold cross2
  ring

theorem unit_cone_inner_gt_half (e a x : Plane) (he : ‖e‖=1) (ha : ‖a‖=1) (hx : ‖x‖=1)
    (hea : (1/2:ℝ) < inner ℝ e a) (r s : ℝ) (hr : 0≤r) (hs : 0≤s)
    (heq : x=r • e+s • a) : (1/2:ℝ) < inner ℝ a x := by
  have hsum := norm_add_le (r • e) (s • a)
  rw [← heq,hx,norm_smul,norm_smul,he,ha,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg hr,abs_of_nonneg hs,mul_one,mul_one] at hsum
  have hα : inner ℝ a e=inner ℝ e a := real_inner_comm _ _
  have hhi := real_inner_le_norm e a
  rw [he,ha,mul_one] at hhi
  have hdot : inner ℝ a x=r*inner ℝ e a+s := by
    rw [heq,inner_add_right,real_inner_smul_right,real_inner_smul_right,hα,
      real_inner_self_eq_norm_sq,ha]
    ring
  have h1 := mul_nonneg hs (sub_nonneg.mpr hhi)
  have h2 := mul_le_mul_of_nonneg_left hsum (by linarith : 0 ≤ inner ℝ e a)
  nlinarith [hdot]

theorem unit_gap_below_axis (e a x : Plane) (he : ‖e‖=1) (ha : ‖a‖=1) (hx : ‖x‖=1)
    (hea : (1/2:ℝ) < inner ℝ e a) (hc : 0<cross2 e a)
    (hax : cross2 a x<0) (hdot : inner ℝ a x<1/2) : cross2 e x<0 := by
  by_contra hn
  let r := cross2 x a/cross2 e a
  let s := cross2 e x/cross2 e a
  have hr : 0≤r := (div_pos (by rw [ucp_cross_swap x a]; linarith) hc).le
  have hs : 0≤s := div_nonneg (le_of_not_gt hn) hc.le
  have h := unit_cone_inner_gt_half e a x he ha hx hea r s hr hs
    (cramer_reconstruct e a x (ne_of_gt hc)).symm
  linarith

theorem unit_gap_above_axis (e a x : Plane) (he : ‖e‖=1) (ha : ‖a‖=1) (hx : ‖x‖=1)
    (hea : (1/2:ℝ) < inner ℝ e a) (hc : cross2 e a<0)
    (hax : 0<cross2 a x) (hdot : inner ℝ a x<1/2) : 0<cross2 e x := by
  by_contra hn
  let r := cross2 x a/cross2 e a
  let s := cross2 e x/cross2 e a
  have hr : 0≤r := (div_pos_of_neg_of_neg (by rw [ucp_cross_swap x a]; linarith) hc).le
  have hs : 0≤s := div_nonneg_of_nonpos (le_of_not_gt hn) hc.le
  have h := unit_cone_inner_gt_half e a x he ha hx hea r s hr hs
    (cramer_reconstruct e a x (ne_of_lt hc)).symm
  linarith

theorem unit_straddling_sum_sub_axis_lt_one (e u v : Plane)
    (he : ‖e‖=1) (hu : ‖u‖=1) (hv : ‖v‖=1)
    (heu : 0 < inner ℝ e u) (hev : 0 < inner ℝ e v)
    (hcu : cross2 e u<0) (hcv : 0<cross2 e v) : ‖e-(u+v)‖<1 := by
  have hdet : 0<cross2 u v := by
    rw [cross2_in_unit_frame e u v he]
    exact sub_pos.mpr (lt_of_lt_of_le (mul_neg_of_neg_of_pos hcu hev)
      (le_of_lt (mul_pos heu hcv)))
  let r := cross2 e v/cross2 u v
  let s := cross2 u e/cross2 u v
  have hr : 0≤r := (div_pos hcv hdet).le
  have hs : 0≤s := (div_pos (by rw [ucp_cross_swap u e]; linarith) hdet).le
  by_contra hn
  rcases unit_cone_far_corner e u v he hu hv (ne_of_gt hdet) r s hr hs
      (cramer_reconstruct u v e (ne_of_gt hdet)).symm (le_of_not_gt hn) with h | h
  · rw [← h,cross2_self] at hcu
    exact lt_irrefl _ hcu
  · rw [← h,cross2_self] at hcv
    exact lt_irrefl _ hcv

end Swanepoel
