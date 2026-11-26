module
public import Swanepoel.FiniteJumpFill
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
@[expose] public section

noncomputable section
namespace Swanepoel
open MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem finite_slice_integral {ι : Type*} [Fintype ι]
    (height jump : ι→ℝ) (f : ℝ→ℝ) (R : ℝ)
    (hheight : ∀ i,-R<height i ∧ height i<R)
    (hzero : ∀ y,y∉Ioo (-R) R → f y=0)
    (hrec : ∀ y,(∀ i,y≠height i) → f y=finiteJumpSum height jump y) :
    (∫ y,f y)=∑ i,jump i*(height i+R) := by
  have hne : ∀ᵐ y : ℝ,∀ i,y≠height i :=
    Filter.eventually_all.mpr (fun i => volume.ae_ne (height i))
  have hae : f=ᵐ[volume] (Ioo (-R) R).indicator (finiteJumpSum height jump) := by
    filter_upwards [hne] with y hy
    by_cases hmem : y∈Ioo (-R) R
    · rw [Set.indicator_of_mem hmem,hrec y hy]
    · rw [Set.indicator_of_notMem hmem,hzero y hmem]
  have hint (i : ι) : IntegrableOn (fun y => if y<height i then jump i else 0) (Ioo (-R) R) := by
    change IntegrableOn ((Iio (height i)).indicator (fun _ : ℝ => jump i)) (Ioo (-R) R)
    exact (integrableOn_const (measure_Ioo_lt_top (μ := (volume : Measure ℝ)) (a := -R) (b := R)).ne).indicator measurableSet_Iio
  have hterm (i : ι) : (∫ y in Ioo (-R) R,if y<height i then jump i else 0)=jump i*(height i+R) := by
    change (∫ y in Ioo (-R) R,(Iio (height i)).indicator (fun _ : ℝ => jump i) y)=_
    rw [setIntegral_indicator measurableSet_Iio]
    have heq : Ioo (-R) R ∩ Iio (height i)=Ioo (-R) (height i) := by
      ext y
      simp only [mem_inter_iff,mem_Ioo,mem_Iio]
      constructor
      · exact fun h => ⟨h.1.1,h.2⟩
      · exact fun h => ⟨⟨h.1,h.2.trans (hheight i).2⟩,h.2⟩
    rw [heq,setIntegral_const]
    simp only [smul_eq_mul,measureReal_def,Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith only [(hheight i).1] : 0≤height i-(-R))]
    ring
  rw [integral_congr_ae hae,integral_indicator measurableSet_Ioo]
  unfold finiteJumpSum
  rw [integral_finsetSum _ (fun i _ => hint i)]
  exact Finset.sum_congr rfl (fun i _ => hterm i)

end Swanepoel
