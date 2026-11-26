module
public import Swanepoel.TerminalDisplacement
@[expose] public section

noncomputable section
namespace Swanepoel

theorem unit_cone_far_corner (u v w : Plane)
    (hu : ‖u‖=1) (hv : ‖v‖=1) (hw : ‖w‖=1) (hvw : cross2 v w≠0)
    (r s : ℝ) (hr : 0≤r) (hs : 0≤s) (heq : u=r • v+s • w)
    (hfar : 1≤‖u-(v+w)‖) : u=v ∨ u=w := by
  have hgram := cross2_sq_add_inner_sq v w
  rw [hv,hw] at hgram
  have hcross : 0<(cross2 v w)^2 := sq_pos_of_ne_zero hvw
  have hlo : -1 < inner ℝ v w := by nlinarith [sq_nonneg (inner ℝ v w+1)]
  have hhi : inner ℝ v w<1 := by nlinarith [sq_nonneg (inner ℝ v w-1)]
  have hcomm : inner ℝ w v=inner ℝ v w := real_inner_comm _ _
  have hnorm : r^2+s^2+2*r*s*inner ℝ v w=1 := by
    have hh := congrArg (fun x : Plane => inner ℝ x x) heq
    simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right] at hh
    simp only [real_inner_self_eq_norm_sq,hu,hv,hw,hcomm] at hh
    nlinarith [hh]
  have hdot : inner ℝ u (v+w)=(r+s)*(1+inner ℝ v w) := by
    rw [heq]
    simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_self_eq_norm_sq,
      hv,hw,hcomm]
    ring
  have hsum := norm_add_sq_real v w
  rw [hv,hw] at hsum
  have hdiff := norm_sub_sq_real u (v+w)
  rw [hu,hsum,hdot] at hdiff
  have hfar2 : 1≤‖u-(v+w)‖^2 := by nlinarith [sq_nonneg (‖u-(v+w)‖-1)]
  have hrs : r+s≤1 := by
    by_contra hh
    have hp := mul_pos (show 0<r+s-1 by linarith)
      (show 0<1+inner ℝ v w by linarith)
    nlinarith [hp]
  have hsq : (r+s)^2≤1 := by
    have hp := mul_nonneg (show 0≤1-(r+s) by linarith)
      (show 0≤1+(r+s) by linarith)
    nlinarith [hp]
  have hprod : r*s=0 := by
    have hnonneg := mul_nonneg hr hs
    have hle : (r*s)*(1-inner ℝ v w)≤0 := by nlinarith
    by_contra hh
    have hp := mul_pos (lt_of_le_of_ne hnonneg (Ne.symm hh))
      (show 0<1-inner ℝ v w by linarith)
    linarith
  rcases mul_eq_zero.mp hprod with hr0 | hs0
  · have hs2 : s^2=1 := by simpa only [hr0,zero_pow (by decide : 2≠0),zero_add,
        mul_zero,zero_mul,add_zero] using hnorm
    have hs1 : s=1 := by
      rcases sq_eq_one_iff.mp hs2 with h | h
      · exact h
      · linarith
    right
    rw [heq,hr0,hs1,zero_smul,one_smul,zero_add]
  · have hr2 : r^2=1 := by simpa only [hs0,zero_pow (by decide : 2≠0),add_zero,
        mul_zero,zero_mul] using hnorm
    have hr1 : r=1 := by
      rcases sq_eq_one_iff.mp hr2 with h | h
      · exact h
      · linarith
    left
    rw [heq,hr1,hs0,one_smul,zero_smul,add_zero]

theorem unit_cap_neighbours_match (u v w : Plane)
    (hu : ‖u‖=1) (hv : ‖v‖=1) (hw : ‖w‖=1)
    (axis : Plane →ₗ[ℝ] ℝ) (hvAxis : 0<axis v)
    (huAxis : 0≤axis u) (hwAxis : axis w≤0)
    (hvw : cross2 v w≠0) (hside : 0<cross2 v u/cross2 v w)
    (hfar : 1≤‖u-(v+w)‖) : u=w ∧ axis u=0 := by
  let r := cross2 u w/cross2 v w
  let s := cross2 v u/cross2 v w
  have heq : u=r • v+s • w := (cramer_reconstruct v w u hvw).symm
  have hs : 0≤s := le_of_lt hside
  have hm : axis u=r*axis v+s*axis w := by
    rw [heq]
    simp only [map_add,map_smul,smul_eq_mul]
  have hr : 0≤r := by
    have hp : 0≤r*axis v := by
      have hn := mul_nonpos_of_nonneg_of_nonpos hs hwAxis
      linarith
    by_contra hh
    have hn := mul_neg_of_neg_of_pos (show r<0 by linarith) hvAxis
    linarith
  have he : u=w := by
    rcases unit_cone_far_corner u v w hu hv hw hvw r s hr hs heq hfar with h | h
    · have hz : cross2 v u=0 := by rw [h,cross2_self]
      rw [hz,zero_div] at hside
      exact False.elim (lt_irrefl _ hside)
    · exact h
  refine ⟨he,?_⟩
  rw [he] at huAxis ⊢
  linarith

end Swanepoel
