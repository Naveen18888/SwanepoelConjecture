module
public import Swanepoel.TrackCutWindingJumpCore
@[expose] public section

noncomputable section
namespace Swanepoel
open Filter
open scoped Topology

theorem PlaneChain.segment_loop_winding_jump {a b : Plane} (hne : a≠b)
    (rest : PlaneChain b a) (hm : (1/2 : ℝ) • (a+b)∉rest.trace) :
    ∃ ε : ℝ, 0<ε ∧ ∀ s : ℝ, 0<s → s<ε →
      let p := (PlaneChain.single a b).append rest
      windingNormalProbe a b s∉p.trace ∧ windingNormalProbe a b (-s)∉p.trace ∧
        p.windingIndex (windingNormalProbe a b (-s))=
          p.windingIndex (windingNormalProbe a b s)+1 ∧
        p.windingIndex (windingNormalProbe a b s)%2≠
          p.windingIndex (windingNormalProbe a b (-s))%2 := by
  let p := (PlaneChain.single a b).append rest
  have hU : IsOpen {s : ℝ | windingNormalProbe a b s∉rest.trace} :=
    rest.isCompact_trace.isClosed.isOpen_compl.preimage (continuous_windingNormalProbe a b)
  have h0 : (0 : ℝ)∈{s : ℝ | windingNormalProbe a b s∉rest.trace} := by
    simpa only [windingNormalProbe,zero_smul,add_zero,Set.mem_ofPred_eq] using hm
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU 0 h0
  have hfree (s : ℝ) (hs : 0<s) (hsε : s<ε) :
      windingNormalProbe a b s∉p.trace ∧ windingNormalProbe a b (-s)∉p.trace := by
    have hplus : windingNormalProbe a b s∉rest.trace :=
      hball (by simpa [Metric.mem_ball,Real.dist_eq,abs_of_pos hs] using hsε)
    have hminus : windingNormalProbe a b (-s)∉rest.trace :=
      hball (by simpa [Metric.mem_ball,Real.dist_eq,abs_neg,abs_of_pos hs] using hsε)
    simp only [p,PlaneChain.trace_append,PlaneChain.trace_single]
    exact ⟨fun h => h.elim (windingNormalProbe_not_mem_segment a b hne hs.ne') hplus,
      fun h => h.elim (windingNormalProbe_not_mem_segment a b hne (neg_ne_zero.mpr hs.ne')) hminus⟩
  let P := windingNormalProbe a b '' Set.Ioo (0 : ℝ) ε
  let M := (fun s : ℝ => windingNormalProbe a b (-s)) '' Set.Ioo (0 : ℝ) ε
  have hP : IsPreconnected P :=
    isPreconnected_Ioo.image _ (continuous_windingNormalProbe a b).continuousOn
  have hM : IsPreconnected M :=
    isPreconnected_Ioo.image _ ((continuous_windingNormalProbe a b).comp continuous_neg).continuousOn
  have hdP : Disjoint P p.trace := by
    apply Set.disjoint_left.mpr
    rintro z ⟨s,hs,rfl⟩ hz
    exact (hfree s hs.1 hs.2).1 hz
  have hdM : Disjoint M p.trace := by
    apply Set.disjoint_left.mpr
    rintro z ⟨s,hs,rfl⟩ hz
    exact (hfree s hs.1 hs.2).2 hz
  let v := ε/2
  have hv0 : 0<v := by dsimp [v]; positivity
  have hvε : v<ε := by dsimp [v]; linarith
  have hpv : windingNormalProbe a b v∈P := ⟨v,⟨hv0,hvε⟩,rfl⟩
  have hmv : windingNormalProbe a b (-v)∈M := ⟨v,⟨hv0,hvε⟩,rfl⟩
  have heqP : (fun s : ℝ => p.angle (windingNormalProbe a b s))=ᶠ[𝓝[>] 0]
      (fun _ => p.angle (windingNormalProbe a b v)) := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hε)] with s hs hsε
    exact p.closed_angle_constant hP hdP ⟨s,⟨hs,hsε⟩,rfl⟩ hpv
  have heqM : (fun s : ℝ => p.angle (windingNormalProbe a b (-s)))=ᶠ[𝓝[>] 0]
      (fun _ => p.angle (windingNormalProbe a b (-v))) := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hε)] with s hs hsε
    exact p.closed_angle_constant hM hdM ⟨s,⟨hs,hsε⟩,rfl⟩ hmv
  have hlimits := PlaneChain.segment_loop_angle_limits hne rest hm
  have hAP := tendsto_nhds_unique hlimits.1 (tendsto_const_nhds.congr' heqP.symm)
  have hAM := tendsto_nhds_unique hlimits.2 (tendsto_const_nhds.congr' heqM.symm)
  have hkP := p.windingIndex_spec (hfree v hv0 hvε).1
  have hkM := p.windingIndex_spec (hfree v hv0 hvε).2
  have hmul : ((p.windingIndex (windingNormalProbe a b (-v)) : ℝ)-
      (p.windingIndex (windingNormalProbe a b v) : ℝ))*(2*Real.pi)=1*(2*Real.pi) := by
    rw [sub_mul,hkM,hkP]
    linarith
  have hcast := mul_right_cancel₀ (by positivity : (2*Real.pi : ℝ)≠0) hmul
  have hint : p.windingIndex (windingNormalProbe a b (-v))-
      p.windingIndex (windingNormalProbe a b v)=1 := by exact_mod_cast hcast
  refine ⟨ε,hε,?_⟩
  intro s hs hsε
  have hkPs := p.windingIndex_constant hP hdP ⟨s,⟨hs,hsε⟩,rfl⟩ hpv
  have hkMs := p.windingIndex_constant hM hdM ⟨s,⟨hs,hsε⟩,rfl⟩ hmv
  refine ⟨(hfree s hs hsε).1,(hfree s hs hsε).2,?_,?_⟩ <;> dsimp only [p] at *
  · omega
  · omega

end Swanepoel
