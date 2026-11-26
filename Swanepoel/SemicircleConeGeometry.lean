module
public import Swanepoel.DirectionPacking
@[expose] public section

noncomputable section
namespace Swanepoel

theorem unit_cone_bisector_positive (a b u : Plane)
    (ha : ‖a‖=1) (hb : ‖b‖=1) (hu : ‖u‖=1)
    (hab : -(1/2 : ℝ) < inner ℝ a b)
    (hcone : Real.sqrt 3/2 ≤ inner ℝ a u) :
    0 < inner ℝ (a+b) u := by
  by_contra hn
  have hsum : inner ℝ a u+inner ℝ b u ≤ 0 := by
    simpa only [inner_add_left] using le_of_not_gt hn
  have hdot : inner ℝ u (a-b) ≤ ‖a-b‖ := by
    have hc := (le_abs_self (inner ℝ u (a-b))).trans (abs_real_inner_le_norm u (a-b))
    simpa only [hu,one_mul] using hc
  have hcommA : inner ℝ u a=inner ℝ a u := real_inner_comm _ _
  have hcommB : inner ℝ u b=inner ℝ b u := real_inner_comm _ _
  rw [inner_sub_right,hcommA,hcommB] at hdot
  have hroot : Real.sqrt 3 ≤ ‖a-b‖ := by linarith
  have hs := norm_sub_sq_real a b
  rw [ha,hb] at hs
  have hsq : ‖a-b‖^2 < 3 := by nlinarith
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ)≤3)
  have hmul := mul_nonneg (sub_nonneg.mpr hroot)
    (add_nonneg (norm_nonneg (a-b)) (Real.sqrt_nonneg 3))
  nlinarith

theorem two_unit_cones_bisector_positive (a b u : Plane)
    (ha : ‖a‖=1) (hb : ‖b‖=1) (hu : ‖u‖=1)
    (hab : -(1/2 : ℝ) < inner ℝ a b)
    (hcone : Real.sqrt 3/2 ≤ inner ℝ a u ∨ Real.sqrt 3/2 ≤ inner ℝ b u) :
    0 < inner ℝ (a+b) u := by
  rcases hcone with h | h
  · exact unit_cone_bisector_positive a b u ha hb hu hab h
  · have hcomm : inner ℝ b a=inner ℝ a b := real_inner_comm _ _
    simpa only [add_comm] using
      unit_cone_bisector_positive b a u hb ha hu (by rw [hcomm]; exact hab) h

theorem unit_bisector_ne_zero (a b : Plane) (ha : ‖a‖=1) (hb : ‖b‖=1)
    (hab : -(1/2 : ℝ) < inner ℝ a b) : a+b≠0 := by
  intro he
  have hs := norm_add_sq_real a b
  rw [he,norm_zero,ha,hb] at hs
  nlinarith

theorem opposite_bisector_misses_two_unit_cones (a b u : Plane)
    (ha : ‖a‖=1) (hb : ‖b‖=1) (hu : ‖u‖=1)
    (hab : -(1/2 : ℝ) < inner ℝ a b)
    (hopp : 0 < inner ℝ (-(a+b)) u) :
    inner ℝ a u < Real.sqrt 3/2 ∧ inner ℝ b u < Real.sqrt 3/2 := by
  have hn : ¬(Real.sqrt 3/2 ≤ inner ℝ a u ∨ Real.sqrt 3/2 ≤ inner ℝ b u) := by
    intro hc
    have hp := two_unit_cones_bisector_positive a b u ha hb hu hab hc
    rw [inner_neg_left] at hopp
    linarith
  exact ⟨lt_of_not_ge (fun h => hn (Or.inl h)),lt_of_not_ge (fun h => hn (Or.inr h))⟩

end Swanepoel
