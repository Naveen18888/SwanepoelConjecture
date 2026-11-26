module
public import Swanepoel.L38AreaSupport
public import Swanepoel.FaceMeasureShoelace
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Convex.Integral
@[expose] public section

noncomputable section
namespace Swanepoel
open MeasureTheory Set
attribute [local instance] Classical.propDecidable

def l38SliceHeight (p : ℝ × ℝ) : List (ℝ × ℝ) → ℝ → ℝ
  | [] => fun _ => p.2
  | q::L => fun x => if x ≤ q.1 then p.2+(q.2-p.2)/(q.1-p.1)*(x-p.1)
      else l38SliceHeight q L x

def l38SliceEnd (p : ℝ × ℝ) : List (ℝ × ℝ) → ℝ × ℝ
  | [] => p
  | q::L => l38SliceEnd q L

def l38SliceChain (p : ℝ × ℝ) : List (ℝ × ℝ) → Prop
  | [] => True
  | q::L => p.1 < q.1 ∧ l38SliceChain q L

def l38SliceTrapezoids (p : ℝ × ℝ) : List (ℝ × ℝ) → ℝ
  | [] => 0
  | q::L => (q.1-p.1)*(p.2+q.2)/2+l38SliceTrapezoids q L

theorem l38SliceChain_end_le (p : ℝ × ℝ) (L : List (ℝ × ℝ))
    (hc : l38SliceChain p L) : p.1 ≤ (l38SliceEnd p L).1 := by
  induction L generalizing p with
  | nil => exact le_rfl
  | cons q L ih => exact hc.1.le.trans (ih q hc.2)

theorem l38SliceHeight_left (p : ℝ × ℝ) (L : List (ℝ × ℝ))
    (hc : l38SliceChain p L) : l38SliceHeight p L p.1 = p.2 := by
  cases L with
  | nil => rfl
  | cons q L => simp [l38SliceHeight,hc.1.le]

theorem l38SliceHeight_continuous (p : ℝ × ℝ) (L : List (ℝ × ℝ))
    (hc : l38SliceChain p L) : Continuous (l38SliceHeight p L) := by
  induction L generalizing p with
  | nil => exact continuous_const
  | cons q L ih =>
    apply continuous_if_le continuous_id continuous_const
      (continuous_const.add (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn
      (ih q hc.2).continuousOn
    intro x hx
    change x=q.1 at hx
    rw [hx,l38SliceHeight_left q L hc.2]
    change p.2+(q.2-p.2)/(q.1-p.1)*(q.1-p.1)=q.2
    have hne : q.1-p.1 ≠ 0 := sub_ne_zero.mpr hc.1.ne'
    field_simp
    ring

theorem l38SliceHeight_graph_mem (C : Set Plane) (hC : Convex ℝ C)
    (p : ℝ × ℝ) (L : List (ℝ × ℝ)) (hc : l38SliceChain p L) (s : ℝ)
    (hv : ∀ q ∈ p::L, cartPoint q.1 (s*q.2) ∈ C)
    {x : ℝ} (hx : x ∈ Icc p.1 (l38SliceEnd p L).1) :
    cartPoint x (s*l38SliceHeight p L x) ∈ C := by
  induction L generalizing p with
  | nil =>
    have hxp : x=p.1 := le_antisymm hx.2 hx.1
    simpa [l38SliceHeight,hxp] using hv p (by simp)
  | cons q L ih =>
    by_cases hfirst : x ≤ q.1
    · let a := (x-p.1)/(q.1-p.1)
      have hd : 0 < q.1-p.1 := sub_pos.mpr hc.1
      have ha0 : 0 ≤ a := div_nonneg (sub_nonneg.mpr hx.1) hd.le
      have ha1 : a ≤ 1 := (div_le_one hd).mpr (by linarith only [hfirst])
      have hmem := hC (hv p (by simp)) (hv q (by simp))
        (sub_nonneg.mpr ha1) ha0 (show (1-a)+a=1 by ring)
      convert hmem using 1
      ext i
      fin_cases i <;>
        simp [l38SliceHeight,hfirst,cartPoint,a] <;>
        field_simp <;> ring
    · simpa only [l38SliceHeight,hfirst,ite_false] using
        ih q hc.2 (fun r hr => hv r (List.mem_cons_of_mem _ hr))
          ⟨(not_le.mp hfirst).le,hx.2⟩

theorem l38Slice_line_integral (p q : ℝ × ℝ) (hpq : p.1 < q.1) :
    (∫ x in p.1..q.1, p.2+(q.2-p.2)/(q.1-p.1)*(x-p.1)) =
      (q.1-p.1)*(p.2+q.2)/2 := by
  have hi : IntervalIntegrable (fun x : ℝ => x) volume p.1 q.1 := continuous_id.intervalIntegrable _ _
  have hc : IntervalIntegrable (fun _ : ℝ => p.2) volume p.1 q.1 := continuous_const.intervalIntegrable _ _
  have hp : IntervalIntegrable (fun _ : ℝ => p.1) volume p.1 q.1 := continuous_const.intervalIntegrable _ _
  have hs : IntervalIntegrable (fun x : ℝ => (q.2-p.2)/(q.1-p.1)*(x-p.1)) volume p.1 q.1 :=
    (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hc hs,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub hi hp,
    integral_id,intervalIntegral.integral_const,intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  have hne : q.1-p.1 ≠ 0 := sub_ne_zero.mpr hpq.ne'
  field_simp
  ring

theorem l38SliceHeight_integral (p : ℝ × ℝ) (L : List (ℝ × ℝ))
    (hc : l38SliceChain p L) :
    (∫ x in p.1..(l38SliceEnd p L).1, l38SliceHeight p L x) =
      l38SliceTrapezoids p L := by
  induction L generalizing p with
  | nil => simp [l38SliceEnd,l38SliceTrapezoids]
  | cons q L ih =>
    have hcont := l38SliceHeight_continuous p (q::L) hc
    have hleft : (∫ x in p.1..q.1,l38SliceHeight p (q::L) x) =
        (q.1-p.1)*(p.2+q.2)/2 := by
      rw [← l38Slice_line_integral p q hc.1]
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hc.1.le] at hx
      simp [l38SliceHeight,hx.2]
    have hright : (∫ x in q.1..(l38SliceEnd q L).1,l38SliceHeight p (q::L) x) =
        ∫ x in q.1..(l38SliceEnd q L).1,l38SliceHeight q L x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (l38SliceChain_end_le q L hc.2)] at hx
      by_cases hfirst : x ≤ q.1
      · have heq : x=q.1 := le_antisymm hfirst hx.1
        rw [heq,l38SliceHeight_left q L hc.2]
        simp only [l38SliceHeight,le_refl,ite_true]
        have hne : q.1-p.1 ≠ 0 := sub_ne_zero.mpr hc.1.ne'
        field_simp
        ring
      · simp [l38SliceHeight,hfirst]
    change (∫ x in p.1..(l38SliceEnd q L).1,l38SliceHeight p (q::L) x) = _
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable p.1 q.1)
      (hcont.intervalIntegrable q.1 (l38SliceEnd q L).1),hleft,hright,ih q hc.2]
    rfl

end Swanepoel
