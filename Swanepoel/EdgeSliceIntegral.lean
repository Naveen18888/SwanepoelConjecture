module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
@[expose] public section

noncomputable section
namespace Swanepoel
open MeasureTheory Set
attribute [local instance] Classical.propDecidable

theorem integral_affine_Ioo (a b C D : ℝ) (hab : a≤b) :
    (∫ x in Ioo a b,C+D*x)=(b-a)*(C+D*(a+b)/2) := by
  have hD : IntervalIntegrable (fun x : ℝ => D*x) volume a b := by
    have hc : Continuous (fun x : ℝ => D*x) := by fun_prop
    exact hc.intervalIntegrable a b
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hab]
  rw [intervalIntegral.integral_add (f := fun _ : ℝ => C) (g := fun x : ℝ => D*x) intervalIntegrable_const hD,
    intervalIntegral.integral_const,intervalIntegral.integral_const_mul,integral_id]
  simp only [smul_eq_mul]
  ring

theorem oriented_edge_slice_integral (a b c d R j : ℝ) :
    (∫ x in Ioo (min a b) (max a b),
      (if 0<b-a then j else -j)*(c+(x-a)/(b-a)*(d-c)+R))=
        j*(b-a)*((c+d)/2+R) := by
  have hbody : (fun x : ℝ => c+(x-a)/(b-a)*(d-c)+R)=
      (fun x => (c+R-a*(d-c)/(b-a))+((d-c)/(b-a))*x) := by
    funext x
    ring
  rcases lt_trichotomy a b with hab | hab | hab
  · have hd : 0<b-a := sub_pos.mpr hab
    rw [min_eq_left hab.le,max_eq_right hab.le]
    simp only [ite_eq_left hd]
    rw [integral_const_mul,hbody,integral_affine_Ioo _ _ _ _ hab.le]
    field_simp [ne_of_gt hd]
    ring
  · subst b
    simp
  · have hd : b-a<0 := sub_neg.mpr hab
    rw [min_eq_right hab.le,max_eq_left hab.le]
    simp only [ite_eq_right (not_lt_of_ge hd.le)]
    rw [integral_const_mul,hbody,integral_affine_Ioo _ _ _ _ hab.le]
    field_simp [ne_of_lt hd]
    ring

end Swanepoel
