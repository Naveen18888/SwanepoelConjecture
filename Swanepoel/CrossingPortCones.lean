module
public import Swanepoel.FaceDirectionalSupport
public import Swanepoel.SemicircleConeGeometry
@[expose] public section

noncomputable section
namespace Swanepoel

theorem crossing_port_normal_abs_gt_sqrt_three_half {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) (cut : TrackComponent G) (e : OrientedEdge G)
    (hcross : ComponentCrosses cut (edgeComponent e)) :
    Real.sqrt 3/2 < |inner ℝ (componentVector cut) (sourceNormal e)| := by
  have hangle := component_crossing_angle ht hcross
  have hsmall : |inner ℝ (componentVector cut) (carriedVector e)| < 1/2 := by
    rcases component_sameLine e (edgeComponent e) rfl with he | he
    · simpa only [he] using hangle
    · simpa only [he,inner_neg_right,abs_neg] using hangle
  have hg := cross2_sq_add_inner_sq (componentVector cut) (carriedVector e)
  rw [componentVector_norm,carriedVector_norm] at hg
  have hsquare : (3/4 : ℝ) < (cross2 (componentVector cut) (carriedVector e))^2 := by
    have hi := (abs_lt.mp hsmall)
    nlinarith [mul_pos (by linarith : 0 < 1/2-inner ℝ (componentVector cut) (carriedVector e))
      (by linarith : 0 < 1/2+inner ℝ (componentVector cut) (carriedVector e))]
  rw [sourceNormal_inner_eq_cross]
  have hroot := Real.sq_sqrt (by norm_num : (0 : ℝ)≤3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  nlinarith [sq_abs (cross2 (componentVector cut) (carriedVector e)),
    abs_nonneg (cross2 (componentVector cut) (carriedVector e))]

theorem crossing_port_normal_positive_cone {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) (cut : TrackComponent G) (e : OrientedEdge G)
    (hcross : ComponentCrosses cut (edgeComponent e))
    (hpositive : 0 < inner ℝ (componentVector cut) (sourceNormal e)) :
    Real.sqrt 3/2 < inner ℝ (componentVector cut) (sourceNormal e) := by
  simpa only [abs_of_pos hpositive] using
    crossing_port_normal_abs_gt_sqrt_three_half ht cut e hcross

theorem crossing_port_normal_negative_cone {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) (cut : TrackComponent G) (e : OrientedEdge G)
    (hcross : ComponentCrosses cut (edgeComponent e))
    (hnegative : inner ℝ (componentVector cut) (sourceNormal e) < 0) :
    Real.sqrt 3/2 < inner ℝ (-componentVector cut) (sourceNormal e) := by
  have h := crossing_port_normal_abs_gt_sqrt_three_half ht cut e hcross
  simpa only [abs_of_neg hnegative,inner_neg_left] using h

end Swanepoel
