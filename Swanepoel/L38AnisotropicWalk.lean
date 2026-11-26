module
public import Swanepoel.L38AnisotropicNormalized
public import Mathlib.Algebra.BigOperators.Field
@[expose] public section

noncomputable section
namespace Swanepoel
open MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem l38_cyclicSignedArea_smul {ι : Type*} [Fintype ι]
    (next : Equiv.Perm ι) (p : ι→Plane) (r : ℝ) :
    cyclicSignedArea next (fun i => r • p i)=r^2*cyclicSignedArea next p := by
  have hpoint (i : ι) : cross2 (r • p i) (r • p (next i))=r^2*cross2 (p i) (p (next i)) := by
    rw [cross2_smul_left,cross2_smul_right]
    ring
  unfold cyclicSignedArea cyclicDoubleArea
  simp_rw [hpoint]
  rw [← Finset.mul_sum]
  ring

theorem l38_cyclicSignedArea_sub {ι : Type*} [Fintype ι]
    (next : Equiv.Perm ι) (p : ι→Plane) (c : Plane) :
    cyclicSignedArea next (fun i => p i-c)=cyclicSignedArea next p := by
  unfold cyclicSignedArea
  rw [cyclicDoubleArea_sub]

theorem l38_cyclicSignedArea_zero_of_x_constant {ι : Type*} [Fintype ι]
    (next : Equiv.Perm ι) (p : ι→Plane) (c : ℝ) (hc : ∀ i,p i 0=c) :
    cyclicSignedArea next p=0 := by
  have hz : (∑ i,(p (next i) 1-p i 1))=0 := by
    rw [Finset.sum_sub_distrib,Equiv.sum_comp next (fun i => p i 1),sub_self]
  have hpoint (i : ι) : cross2 (p i) (p (next i))=c*(p (next i) 1-p i 1) := by
    unfold cross2
    rw [hc i,hc (next i)]
    ring
  unfold cyclicSignedArea cyclicDoubleArea
  simp_rw [hpoint]
  rw [← Finset.mul_sum,hz,mul_zero,zero_div]

theorem l38_bank_walk_area_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (next : Equiv.Perm ι) (hcycle : next.IsCycleOn Set.univ) (p : ι→Plane)
    (bank : ι→Prop) (l : ι→ℝ) (d : ι→Plane)
    (hl : ∀ i,0≤l i) (hd : ∀ i,‖d i‖=1)
    (hedge : ∀ i,p (next i)-p i=l i • d i)
    (hbank : ∀ i,bank i → rightNormalMap (d i)∈l38BankArc l38SupportAxis) :
    4*l38CertificateArea*cyclicSignedArea next p≤
      (∑ i,if bank i then l i/3 else l i)^2 := by
  obtain ⟨imin,_,hmin⟩ := Finset.exists_min_image Finset.univ (fun i => p i 0) Finset.univ_nonempty
  obtain ⟨imax,_,hmax⟩ := Finset.exists_max_image Finset.univ (fun i => p i 0) Finset.univ_nonempty
  have hlo (i : ι) : p imin 0≤p i 0 := hmin i (Finset.mem_univ i)
  have hhi (i : ι) : p i 0≤p imax 0 := hmax i (Finset.mem_univ i)
  rcases eq_or_lt_of_le (hlo imax) with heq | hwidth
  · have hxconst (i : ι) : p i 0=p imin 0 := le_antisymm ((hhi i).trans_eq heq.symm) (hlo i)
    rw [l38_cyclicSignedArea_zero_of_x_constant next p _ hxconst,mul_zero]
    exact sq_nonneg _
  · let t : ℝ := (3/4)*(p imax 0-p imin 0)
    let c : Plane := cartPoint (p imin 0+t) 0
    let p' : ι→Plane := fun i => t⁻¹ • (p i-c)
    have ht : 0<t := by dsimp [t]; positivity
    have htne : t≠0 := ne_of_gt ht
    have hspan : 4*t=3*(p imax 0-p imin 0) := by dsimp [t]; ring
    have hcoord (i : ι) : p' i 0*t=p i 0-(p imin 0+t) := by
      dsimp [p',c]
      field_simp
    have hp' (i : ι) : p' i 0∈Icc (-1) (1/3) := by
      constructor
      · apply (mul_le_mul_iff_right₀ ht).mp
        nlinarith only [hcoord i,hlo i]
      · apply (mul_le_mul_iff_right₀ ht).mp
        nlinarith only [hcoord i,hhi i,hspan]
    have hmin' : p' imin 0= -1 := by
      apply mul_right_cancel₀ htne
      rw [hcoord]
      ring
    have hmax' : p' imax 0=1/3 := by
      apply mul_right_cancel₀ htne
      rw [hcoord]
      nlinarith only [hspan]
    have hedge' (i : ι) : p' (next i)-p' i=(l i/t) • d i := by
      calc
        _ = t⁻¹ • (p (next i)-p i) := by dsimp [p']; module
        _ = (l i/t) • d i := by rw [hedge i,smul_smul]; congr 1; ring
    have hcal := l38_normalized_bank_area_bound next hcycle p' hp' imin imax hmin' hmax'
      bank (fun i => l i/t) d (fun i => div_nonneg (hl i) ht.le) hd hedge' hbank
    have harea : cyclicSignedArea next p'=t⁻¹^2*cyclicSignedArea next p := by
      dsimp [p']
      rw [l38_cyclicSignedArea_smul,l38_cyclicSignedArea_sub]
    have hcost (i : ι) : (if bank i then (l i/t)/3 else l i/t)=
        (if bank i then l i/3 else l i)/t := by split_ifs <;> ring
    rw [harea] at hcal
    simp_rw [hcost] at hcal
    rw [← Finset.sum_div] at hcal
    have hh := mul_le_mul_of_nonneg_right hcal (sq_nonneg t)
    convert hh using 1 <;> field_simp

end Swanepoel
