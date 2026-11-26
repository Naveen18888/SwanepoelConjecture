module
public import Swanepoel.Arithmetic
@[expose] public section

noncomputable section
namespace Swanepoel

theorem moderate_bank_bound (R k d : ℝ)
    (hR : R ≤ (2379 / 10000 : ℝ) * k ^ 2)
    (hlo : (39 / 100 : ℝ) * k ≤ d)
    (hhi : d ≤ (61 / 100 : ℝ) * k) : R ≤ d * (k - d) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)]

def bankU (ρ x H : ℝ) : ℝ :=
  9 * ρ ^ 2 / 8 + (1 + H) * ρ / 2 +
    (411 / 2500 : ℝ) * (11 * ρ / 6 + 2 - H - 2 * x / 3) ^ 2

def bankGap (ρ x H : ℝ) : ℝ := (2 * ρ + x) * (1 + ρ - x) - bankU ρ x H

def bankH0 (x : ℝ) : ℝ := max ((1 + x) / 4) (2 * x - 1)

theorem bankGap_interpolation (ρ a b x y t : ℝ) :
    bankGap ρ ((1-t)*x+t*y) (a*((1-t)*x+t*y)+b) -
      ((1-t)*bankGap ρ x (a*x+b) + t*bankGap ρ y (a*y+b)) =
    t*(1-t)*(1+(411/2500 : ℝ)*(a+2/3)^2)*(y-x)^2 := by
  unfold bankGap bankU
  ring

theorem bankGap_above_chord (ρ a b x y t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1-t)*bankGap ρ x (a*x+b) + t*bankGap ρ y (a*y+b) ≤
      bankGap ρ ((1-t)*x+t*y) (a*((1-t)*x+t*y)+b) := by
  have hfactor : 0 ≤ 1 + (411/2500 : ℝ)*(a+2/3)^2 := by positivity
  have hn := mul_nonneg
    (mul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr ht1)) hfactor) (sq_nonneg (y-x))
  have he := bankGap_interpolation ρ a b x y t
  linarith

theorem bankGap_segment_nonneg (ρ a b lo hi x : ℝ) (hlohi : lo < hi)
    (hxlo : lo ≤ x) (hxhi : x ≤ hi)
    (hlo : 0 ≤ bankGap ρ lo (a*lo+b))
    (hhi : 0 ≤ bankGap ρ hi (a*hi+b)) : 0 ≤ bankGap ρ x (a*x+b) := by
  let t := (x-lo)/(hi-lo)
  have hden : 0 < hi-lo := sub_pos.mpr hlohi
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hxlo) (le_of_lt hden)
  have ht1 : t ≤ 1 := (div_le_iff₀ hden).mpr (by linarith)
  have ht : t*(hi-lo) = x-lo := div_mul_cancel₀ _ (ne_of_gt hden)
  have he : (1-t)*lo+t*hi = x := by nlinarith [ht]
  have h := bankGap_above_chord ρ a b lo hi t ht0 ht1
  rw [he] at h
  exact le_trans (add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) hlo)
    (mul_nonneg ht0 hhi)) h

theorem bankGap_left_pos (ρ : ℝ) :
    0 < bankGap ρ (61/100-17*ρ/100) ((1+(61/100-17*ρ/100))/4) := by
  unfold bankGap bankU
  nlinarith [sq_nonneg (ρ - 31620151/464225647)]

theorem bankGap_mid_pos (ρ : ℝ) : 0 < bankGap ρ (5/7) (3/7) := by
  unfold bankGap bankU
  nlinarith [sq_nonneg (ρ - 9322/67711)]

theorem bankGap_right_pos (ρ : ℝ) : 0 < bankGap ρ (4/5) (3/5) := by
  unfold bankGap bankU
  nlinarith [sq_nonneg (ρ - 9182/48365)]

theorem bankGap_nonneg (ρ x : ℝ) (hρ : 0 ≤ ρ)
    (hxlo : 61/100-17*ρ/100 ≤ x) (hxhi : x ≤ 4/5) :
    0 ≤ bankGap ρ x (bankH0 x) := by
  by_cases hx : x ≤ 5/7
  · have hH : bankH0 x = (1+x)/4 := max_eq_left (by linarith)
    rw [hH]
    have hl : 0 ≤ bankGap ρ (61/100-17*ρ/100)
        ((1/4)*(61/100-17*ρ/100)+1/4) := by
      convert le_of_lt (bankGap_left_pos ρ) using 1; congr 1; ring
    have hr : 0 ≤ bankGap ρ (5/7) ((1/4)*(5/7)+1/4) := by
      norm_num
      exact le_of_lt (bankGap_mid_pos ρ)
    have hg := bankGap_segment_nonneg ρ (1/4) (1/4)
      (61/100-17*ρ/100) (5/7) x (by linarith) hxlo hx hl hr
    convert hg using 1; congr 1; ring
  · have hH : bankH0 x = 2*x-1 := max_eq_right (by linarith)
    rw [hH]
    have hl : 0 ≤ bankGap ρ (5/7) (2*(5/7)+(-1)) := by
      norm_num
      exact le_of_lt (bankGap_mid_pos ρ)
    have hr : 0 ≤ bankGap ρ (4/5) (2*(4/5)+(-1)) := by
      norm_num
      exact le_of_lt (bankGap_right_pos ρ)
    have hg := bankGap_segment_nonneg ρ 2 (-1) (5/7) (4/5) x
      (by norm_num) (by linarith) hxhi hl hr
    simpa only [sub_eq_add_neg] using hg

end Swanepoel
