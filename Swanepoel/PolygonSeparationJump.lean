module
public import Swanepoel.PolygonSeparationWinding
@[expose] public section

noncomputable section
namespace Swanepoel
open Filter
open scoped Topology

def normalEndpointRatio (s : ℝ) : ℂ :=
  ((-1/2 : ℂ)-(s : ℂ)*Complex.I)/((1/2 : ℂ)-(s : ℂ)*Complex.I)

theorem normalEndpointRatio_im (s : ℝ) :
    (normalEndpointRatio s).im= -s/(1/4+s^2) := by
  simp [normalEndpointRatio,Complex.div_im,Complex.normSq_apply]
  ring

theorem continuous_normalEndpointRatio : Continuous normalEndpointRatio := by
  apply Continuous.div
  · exact continuous_const.sub (Complex.continuous_ofReal.mul continuous_const)
  · exact continuous_const.sub (Complex.continuous_ofReal.mul continuous_const)
  · intro s hs
    have h := congrArg Complex.re hs
    norm_num at h

theorem normalEndpointRatio_zero : normalEndpointRatio 0 = -1 := by
  norm_num [normalEndpointRatio,Complex.ext_iff,Complex.div_re,Complex.div_im,Complex.normSq_apply]

theorem tendsto_arg_normalEndpointRatio_pos :
    Tendsto (fun s : ℝ => Complex.arg (normalEndpointRatio s))
      (𝓝[>] 0) (𝓝 (-Real.pi)) := by
  have hc := (Real.continuous_arccos.comp
    ((Complex.continuous_re.comp continuous_normalEndpointRatio).div continuous_normalEndpointRatio.norm
      (fun s => ?_)))
  · have hlim : Tendsto (fun s : ℝ => -Real.arccos
        ((normalEndpointRatio s).re/‖normalEndpointRatio s‖)) (𝓝 0) (𝓝 (-Real.pi)) := by
      convert hc.neg.continuousAt.tendsto (x := 0) using 1
      · funext s
        simp only [Function.comp_def,Pi.neg_apply,Pi.div_apply]
      · simp only [Function.comp_def,Pi.neg_apply,Pi.div_apply,normalEndpointRatio_zero,
          Complex.neg_re,Complex.one_re,norm_neg,norm_one,div_one,Real.arccos_neg_one]
    apply hlim.mono_left nhdsWithin_le_nhds |>.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    symm
    apply Complex.arg_of_im_neg
    rw [normalEndpointRatio_im]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hs) (by positivity)
  · apply norm_ne_zero_iff.mpr
    apply div_ne_zero
    · intro hs
      have h := congrArg Complex.re hs
      norm_num at h
    · intro hs
      have h := congrArg Complex.re hs
      norm_num at h

theorem tendsto_arg_normalEndpointRatio_neg :
    Tendsto (fun s : ℝ => Complex.arg (normalEndpointRatio (-s)))
      (𝓝[>] 0) (𝓝 Real.pi) := by
  have hc : Continuous (fun s : ℝ => (normalEndpointRatio (-s)).re/‖normalEndpointRatio (-s)‖) := by
    apply Continuous.div
    · exact Complex.continuous_re.comp (continuous_normalEndpointRatio.comp continuous_neg)
    · exact (continuous_normalEndpointRatio.comp continuous_neg).norm
    · intro s
      apply norm_ne_zero_iff.mpr
      apply div_ne_zero
      · intro hs
        have h := congrArg Complex.re hs
        norm_num at h
      · intro hs
        have h := congrArg Complex.re hs
        norm_num at h
  have hlim : Tendsto (fun s : ℝ => Real.arccos
      ((normalEndpointRatio (-s)).re/‖normalEndpointRatio (-s)‖)) (𝓝 0) (𝓝 Real.pi) := by
    simpa only [Function.comp_def,neg_zero,normalEndpointRatio_zero,Complex.neg_re,Complex.one_re,norm_neg,norm_one,
      div_one,Real.arccos_neg_one] using (Real.continuous_arccos.comp hc).continuousAt.tendsto (x := 0)
  apply hlim.mono_left nhdsWithin_le_nhds |>.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  symm
  apply Complex.arg_of_im_pos
  rw [normalEndpointRatio_im,neg_neg]
  exact div_pos hs (by positivity)

end Swanepoel
