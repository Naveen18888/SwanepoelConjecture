module
public import Swanepoel.L38SupportAreaPolygon
public import Swanepoel.L38AnisotropicSpan
@[expose] public section

noncomputable section
namespace Swanepoel
open MeasureTheory Set
attribute [local instance] Classical.propDecidable

def l38SlicePrimitive (h : ℝ→ℝ) (a x : ℝ) : ℝ := ∫ u in a..x,h u

theorem l38SlicePrimitive_sub (h : ℝ→ℝ) (hc : Continuous h) (a x y : ℝ) :
    l38SlicePrimitive h a y-l38SlicePrimitive h a x=∫ u in x..y,h u :=
  intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable a y) (hc.intervalIntegrable a x)

theorem l38_continuous_cartPoint {f g : ℝ→ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun t => cartPoint (f t) (g t)) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact hf
  · exact hg

theorem l38_exists_slice_quadrature (C : Set Plane) (hC : Convex ℝ C) (hclosed : IsClosed C)
    (h : ℝ→ℝ) (hcont : Continuous h) (a b : ℝ)
    (hgraph : ∀ x∈Icc a b,cartPoint x (h x)∈C ∧ cartPoint x (-h x)∈C)
    (hpos : ∀ x∈Icc a b,0≤h x) {x y : ℝ} (hx : x∈Icc a b) (hy : y∈Icc a b) :
    ∃ q∈C,q 0=(x+y)/2 ∧
      q 1*(y-x)= -|l38SlicePrimitive h a y-l38SlicePrimitive h a x| := by
  let g : ℝ→Plane := fun s => cartPoint (x+(y-x)*s)
    (if x≤y then -h (x+(y-x)*s) else h (x+(y-x)*s))
  have hgc : Continuous g := by
    apply l38_continuous_cartPoint (by fun_prop)
    split_ifs <;> fun_prop
  have hgrange {s : ℝ} (hs : s∈Icc (0:ℝ) 1) : x+(y-x)*s∈Icc a b := by
    have hh := (convex_Icc a b : Convex ℝ (Icc a b)) hx hy (sub_nonneg.mpr hs.2) hs.1
      (show (1-s)+s=1 by ring)
    convert hh using 1; simp only [smul_eq_mul]; ring
  have hgm : ∀ᵐ s ∂volume.restrict (Icc (0:ℝ) 1),g s∈C := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    apply Filter.Eventually.of_forall
    intro s hs
    dsimp [g]
    split_ifs
    · exact (hgraph _ (hgrange hs)).2
    · exact (hgraph _ (hgrange hs)).1
  have havg := hC.set_average_mem hclosed
    (by norm_num : volume (Icc (0:ℝ) 1)≠0)
    (by simp : volume (Icc (0:ℝ) 1)≠⊤) hgm hgc.integrableOn_Icc
  rw [setAverage_eq] at havg
  have hq : (∫ s in (0:ℝ)..1,g s)∈C := by
    simpa only [measureReal_def,Real.volume_Icc,sub_zero,ENNReal.ofReal_one,
      ENNReal.toReal_one,inv_one,one_smul,integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)] using havg
  have hgi : IntervalIntegrable g volume 0 1 := hgc.intervalIntegrable 0 1
  refine ⟨∫ s in (0:ℝ)..1,g s,hq,?_,?_⟩
  · have hproj := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) (0:Fin 2)).intervalIntegral_comp_comm
      hgi
    change (∫ s in (0:ℝ)..1,(g s) 0)=(∫ s in (0:ℝ)..1,g s) 0 at hproj
    rw [← hproj]
    change (∫ s in (0:ℝ)..1,x+(y-x)*s)=(x+y)/2
    have hxc : IntervalIntegrable (fun _ : ℝ => x) volume 0 1 := continuous_const.intervalIntegrable _ _
    have hlin : IntervalIntegrable (fun s : ℝ => (y-x)*s) volume 0 1 :=
      (continuous_const.mul continuous_id).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hxc hlin,
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const,integral_id]
    simp only [smul_eq_mul]
    ring
  · have hproj := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) (1:Fin 2)).intervalIntegral_comp_comm
      hgi
    change (∫ s in (0:ℝ)..1,(g s) 1)=(∫ s in (0:ℝ)..1,g s) 1 at hproj
    rw [← hproj,l38SlicePrimitive_sub h hcont]
    have hsub : (y-x)*(∫ s in (0:ℝ)..1,h (x+(y-x)*s))=∫ u in x..y,h u := by
      simp
    by_cases hxy : x≤y
    · change (∫ s in (0:ℝ)..1,if x≤y then -h (x+(y-x)*s) else h (x+(y-x)*s))*(y-x)=_
      simp only [hxy,ite_true,intervalIntegral.integral_neg]
      have hp : 0≤∫ u in x..y,h u := intervalIntegral.integral_nonneg hxy
        (fun u hu => hpos u ⟨hx.1.trans hu.1,hu.2.trans hy.2⟩)
      rw [abs_of_nonneg hp]
      nlinarith only [hsub]
    · change (∫ s in (0:ℝ)..1,if x≤y then -h (x+(y-x)*s) else h (x+(y-x)*s))*(y-x)=_
      simp only [hxy,ite_false]
      have hp : (∫ u in x..y,h u)≤0 := by
        rw [intervalIntegral.integral_symm]
        exact neg_nonpos.mpr (intervalIntegral.integral_nonneg (not_le.mp hxy).le
          (fun u hu => hpos u ⟨hy.1.trans hu.1,hu.2.trans hx.2⟩))
      rw [abs_of_nonpos hp]
      nlinarith only [hsub]

end Swanepoel
