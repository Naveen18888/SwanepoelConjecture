module
public import Swanepoel.Foundation
@[expose] public section

noncomputable section
namespace Swanepoel

def cross2 (u v : Plane) : ℝ := u 0*v 1-u 1*v 0

theorem cross2_sq_add_inner_sq (u v : Plane) :
    cross2 u v^2+(inner ℝ u v)^2=‖u‖^2*‖v‖^2 := by
  simp [cross2, EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, Fin.sum_univ_two]
  ring

theorem unit_rhombus_area_lower (u v : Plane) (hu : ‖u‖=1) (hv : ‖v‖=1)
    (hminus : 1 < ‖u-v‖) (hplus : 1 < ‖u+v‖) :
    Real.sqrt 3/2 < |cross2 u v| := by
  have hm := norm_sub_sq_real u v
  have hp := norm_add_sq_real u v
  rw [hu,hv] at hm hp
  have hilo : -(1/2 : ℝ) < inner ℝ u v := by
    nlinarith [sq_nonneg (‖u+v‖-1)]
  have hihi : inner ℝ u v < (1/2 : ℝ) := by
    nlinarith [sq_nonneg (‖u-v‖-1)]
  have hd := cross2_sq_add_inner_sq u v
  rw [hu,hv] at hd
  have hdet : (3/4 : ℝ) < cross2 u v^2 := by
    nlinarith [mul_pos (sub_pos.mpr hilo) (sub_pos.mpr hihi)]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsn := Real.sqrt_nonneg (3 : ℝ)
  have hsq : |cross2 u v|^2=cross2 u v^2 := sq_abs _
  nlinarith [abs_nonneg (cross2 u v)]

theorem parallelogram_variance (u v x : Plane) (t s : ℝ) :
    (1-t)*(1-s)*‖x‖^2+t*(1-s)*‖x-u‖^2+
      (1-t)*s*‖x-v‖^2+t*s*‖x-(u+v)‖^2 =
    ‖x-(t • u+s • v)‖^2+t*(1-t)*‖u‖^2+s*(1-s)*‖v‖^2 := by
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_comm]
  ring

theorem unit_cell_covering (u v x : Plane) (hu : ‖u‖=1) (hv : ‖v‖=1)
    (t s : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hx : x=t • u+s • v) :
    ‖x‖<1 ∨ ‖x-u‖<1 ∨ ‖x-v‖<1 ∨ ‖x-(u+v)‖<1 := by
  by_contra hn
  simp only [not_or, not_lt] at hn
  have hsq (z : Plane) (h : 1 ≤ ‖z‖) : 1 ≤ ‖z‖^2 := by
    nlinarith [sq_nonneg (‖z‖-1)]
  have h1 := mul_le_mul_of_nonneg_left (hsq x hn.1)
    (mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hs1))
  have h2 := mul_le_mul_of_nonneg_left (hsq (x-u) hn.2.1)
    (mul_nonneg ht0 (sub_nonneg.mpr hs1))
  have h3 := mul_le_mul_of_nonneg_left (hsq (x-v) hn.2.2.1)
    (mul_nonneg (sub_nonneg.mpr ht1) hs0)
  have h4 := mul_le_mul_of_nonneg_left (hsq (x-(u+v)) hn.2.2.2)
    (mul_nonneg ht0 hs0)
  have hvar := parallelogram_variance u v x t s
  rw [sub_eq_zero.mpr hx, norm_zero, zero_pow (by decide : 2 ≠ 0), hu, hv] at hvar
  nlinarith [sq_nonneg (2*t-1), sq_nonneg (2*s-1)]

end Swanepoel
