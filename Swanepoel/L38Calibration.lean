module
public import Swanepoel.PolygonArea
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem closed_variation_ge_twice_subsum {ι : Type*} [Fintype ι]
    (d : ι→ℝ) (hclosed : ∑ i,d i=0) (S : Finset ι) :
    2*(∑ i∈S,d i)≤∑ i,|d i| := by
  have hsplit := Finset.sum_sdiff (f := d) (Finset.subset_univ S)
  rw [hclosed] at hsplit
  have hasplit := Finset.sum_sdiff (f := fun i => |d i|) (Finset.subset_univ S)
  have hS : (∑ i∈S,d i)≤∑ i∈S,|d i| :=
    Finset.sum_le_sum (fun i _ => le_abs_self (d i))
  have hT : -(∑ i∈Finset.univ\S,d i)≤∑ i∈Finset.univ\S,|d i| := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun i _ => neg_le_abs (d i))
  linarith only [hsplit,hasplit,hS,hT]

theorem cyclic_xdy_eq_signedArea {ι : Type*} [Fintype ι]
    (next : Equiv.Perm ι) (p : ι→Plane) :
    (∑ i,(p i 0+p (next i) 0)/2*(p (next i) 1-p i 1))=cyclicSignedArea next p := by
  have htel : (∑ i,(p (next i) 0*p (next i) 1-p i 0*p i 1))=0 := by
    rw [Finset.sum_sub_distrib,Equiv.sum_comp next (fun i => p i 0*p i 1),sub_self]
  have htwo : 2*(∑ i,(p i 0+p (next i) 0)/2*(p (next i) 1-p i 1))=
      cyclicDoubleArea next p+(∑ i,(p (next i) 0*p (next i) 1-p i 0*p i 1)) := by
    rw [Finset.mul_sum]
    unfold cyclicDoubleArea
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold cross2
    ring
  rw [htel,add_zero] at htwo
  unfold cyclicSignedArea
  linarith only [htwo]

theorem calibration_square_bound (A C t w : ℝ) (hw : 0≤w)
    (hcal : A+t^2*w≤t*C) : 4*w*A≤C^2 := by
  have hslack := mul_nonneg (show 0≤4*w by positivity) (sub_nonneg.mpr hcal)
  nlinarith only [hslack,sq_nonneg (C-2*t*w)]

theorem finite_walk_support_calibration {ι : Type*} [Fintype ι]
    (next : Equiv.Perm ι) (p q : ι→Plane) (cost : ι→ℝ)
    (middle width : ℝ→ℝ) (S : Finset ι) (t w : ℝ) (hw : 0≤w)
    (hqx : ∀ i,q i 0=(p i 0+p (next i) 0)/2)
    (hmoment : ∀ i,q i 1*(p (next i) 0-p i 0)=
      (middle (p (next i) 0)-middle (p i 0))-
      |width (p (next i) 0)-width (p i 0)|)
    (hspan : t^2*w≤2*Finset.sum S (fun (i : ι) => width (p (next i) 0)-width (p i 0)))
    (hsupport : ∀ i,cross2 (q i) (p (next i)-p i)≤t*cost i) :
    4*w*cyclicSignedArea next p≤(∑ i,cost i)^2 := by
  have hmiddle : (∑ i,(middle (p (next i) 0)-middle (p i 0)))=0 := by
    rw [Finset.sum_sub_distrib,Equiv.sum_comp next (fun i => middle (p i 0)),sub_self]
  have hwidth : (∑ i,(width (p (next i) 0)-width (p i 0)))=0 := by
    rw [Finset.sum_sub_distrib,Equiv.sum_comp next (fun i => width (p i 0)),sub_self]
  have hvariation := closed_variation_ge_twice_subsum
    (fun i => width (p (next i) 0)-width (p i 0)) hwidth S
  have hpoint (i : ι) : cross2 (q i) (p (next i)-p i)=
      (p i 0+p (next i) 0)/2*(p (next i) 1-p i 1)-
      (middle (p (next i) 0)-middle (p i 0))+
      |width (p (next i) 0)-width (p i 0)| := by
    have hh := hmoment i
    change q i 0*(p (next i) 1-p i 1)-q i 1*(p (next i) 0-p i 0)=_
    rw [hqx i]
    linarith only [hh]
  have hsum : (∑ i,cross2 (q i) (p (next i)-p i))=
      cyclicSignedArea next p+∑ i,|width (p (next i) 0)-width (p i 0)| := by
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,hmiddle,sub_zero,cyclic_xdy_eq_signedArea]
  have hbound := Finset.sum_le_sum (s := (Finset.univ : Finset ι)) (fun i _ => hsupport i)
  rw [hsum,← Finset.mul_sum] at hbound
  apply calibration_square_bound _ _ t w hw
  linarith only [hbound,hvariation,hspan]

theorem calibrated_area_coefficient (mass A C w : ℝ) (hmass : 0≤mass)
    (hw : (1757/1000:ℝ)≤w)
    (hlower : Real.sqrt 3/2*mass≤A) (hcal : 4*w*A≤C^2) :
    mass≤(411/2500:ℝ)*C^2 := by
  have hroot : (433/250:ℝ)≤Real.sqrt 3 := by
    nlinarith only [Real.sqrt_nonneg (3:ℝ),Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  have hA : (433/500:ℝ)*mass≤A := by
    have hh := mul_le_mul_of_nonneg_right hroot hmass
    linarith only [hh,hlower]
  have hA0 : 0≤A := (mul_nonneg (by norm_num) hmass).trans hA
  have hscaled : 4*(1757/1000:ℝ)*((433/500:ℝ)*mass)≤C^2 := by
    calc
      _ ≤ 4*(1757/1000:ℝ)*A := mul_le_mul_of_nonneg_left hA (by norm_num)
      _ ≤ 4*w*A := mul_le_mul_of_nonneg_right (by linarith only [hw]) hA0
      _ ≤ C^2 := hcal
  nlinarith only [hscaled,hmass]

end Swanepoel
