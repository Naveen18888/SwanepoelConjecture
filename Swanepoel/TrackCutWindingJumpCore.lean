module
public import Swanepoel.TrackCutWindingDefects
public import Swanepoel.PolygonSeparationProof
@[expose] public section

noncomputable section
namespace Swanepoel
open Filter
open scoped Topology

theorem PlaneChain.isCompact_trace {a b : Plane} (p : PlaneChain a b) : IsCompact p.trace := by
  induction p with
  | nil a => exact isCompact_singleton
  | cons a b c p ih =>
    apply IsCompact.union ?_ ih
    rw [segment_eq_image]
    exact isCompact_Icc.image
      (((continuous_const.sub continuous_id).smul continuous_const).add (continuous_id.smul continuous_const))

def windingNormalProbe (a b : Plane) (s : ℝ) : Plane :=
  (1/2 : ℝ) • (a+b)+s • quarterTurn (a-b)

theorem continuous_windingNormalProbe (a b : Plane) : Continuous (windingNormalProbe a b) :=
  continuous_const.add (continuous_id.smul continuous_const)

theorem segmentAngle_windingNormalProbe (a b : Plane) (hne : a≠b) (s : ℝ) :
    segmentAngle a b (windingNormalProbe a b s)=Complex.arg (normalEndpointRatio s) := by
  have hv : planeComplex a-planeComplex b≠0 := sub_ne_zero.mpr (planeComplex_injective.ne hne)
  have hnum : planeComplex b-planeComplex (windingNormalProbe a b s)=
      ((-1/2 : ℂ)-(s : ℂ)*Complex.I)*(planeComplex a-planeComplex b) := by
    simp only [windingNormalProbe,map_add,map_smul,planeComplex_quarterTurn,map_sub,Complex.real_smul]
    push_cast
    ring
  have hden : planeComplex a-planeComplex (windingNormalProbe a b s)=
      ((1/2 : ℂ)-(s : ℂ)*Complex.I)*(planeComplex a-planeComplex b) := by
    simp only [windingNormalProbe,map_add,map_smul,planeComplex_quarterTurn,map_sub,Complex.real_smul]
    push_cast
    ring
  unfold segmentAngle
  rw [hnum,hden,mul_div_mul_right _ _ hv]
  rfl

theorem windingNormalProbe_not_mem_segment (a b : Plane) (hne : a≠b) {s : ℝ} (hs : s≠0) :
    windingNormalProbe a b s∉segment ℝ a b := by
  intro hmem
  rw [segment_eq_image] at hmem
  obtain ⟨t,_,ht⟩ := hmem
  have heq : (windingNormalProbe a b s-(1/2 : ℝ) • (a+b))=(1/2-t) • (a-b) := by
    rw [← ht]
    module
  have hcross := congrArg (cross2 (a-b)) heq
  have heq' : windingNormalProbe a b s-(1/2 : ℝ) • (a+b)=s • quarterTurn (a-b) := by
    dsimp [windingNormalProbe]
    abel
  rw [heq',cross2_smul_right,cross_quarterTurn,cross2_smul_right,cross2_self,mul_zero] at hcross
  have hn : ‖a-b‖^2≠0 := pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))
  exact hs ((mul_eq_zero.mp hcross).resolve_right hn)

theorem PlaneChain.single_angle {a b : Plane} (z : Plane) :
    (PlaneChain.single a b).angle z=segmentAngle a b z := by
  simp [PlaneChain.single,PlaneChain.angle]

theorem PlaneChain.segment_loop_angle_limits {a b : Plane} (hne : a≠b)
    (rest : PlaneChain b a) (hm : (1/2 : ℝ) • (a+b)∉rest.trace) :
    Tendsto (fun s : ℝ => ((PlaneChain.single a b).append rest).angle (windingNormalProbe a b s))
        (𝓝[>] 0) (𝓝 (rest.angle ((1/2 : ℝ) • (a+b))-Real.pi)) ∧
      Tendsto (fun s : ℝ => ((PlaneChain.single a b).append rest).angle (windingNormalProbe a b (-s)))
        (𝓝[>] 0) (𝓝 (rest.angle ((1/2 : ℝ) • (a+b))+Real.pi)) := by
  have hc := rest.continuousAt_angle hm
  have hplus : Tendsto (fun s : ℝ => rest.angle (windingNormalProbe a b s))
      (𝓝 0) (𝓝 (rest.angle ((1/2 : ℝ) • (a+b)))) := by
    simpa only [Function.comp_def,windingNormalProbe,zero_smul,add_zero] using
      (hc.comp_of_eq ((continuous_windingNormalProbe a b).continuousAt (x := (0 : ℝ)))
        (by simp [windingNormalProbe])).tendsto
  have hminus : Tendsto (fun s : ℝ => rest.angle (windingNormalProbe a b (-s)))
      (𝓝 0) (𝓝 (rest.angle ((1/2 : ℝ) • (a+b)))) := by
    simpa only [Function.comp_def,windingNormalProbe,neg_zero,zero_smul,add_zero] using
      (hc.comp_of_eq (((continuous_windingNormalProbe a b).comp continuous_neg).continuousAt (x := (0 : ℝ)))
        (by simp [windingNormalProbe])).tendsto
  have hsegPlus : Tendsto (fun s : ℝ => segmentAngle a b (windingNormalProbe a b s))
      (𝓝[>] 0) (𝓝 (-Real.pi)) := by
    simpa only [segmentAngle_windingNormalProbe a b hne] using tendsto_arg_normalEndpointRatio_pos
  have hsegMinus : Tendsto (fun s : ℝ => segmentAngle a b (windingNormalProbe a b (-s)))
      (𝓝[>] 0) (𝓝 Real.pi) := by
    simpa only [segmentAngle_windingNormalProbe a b hne] using tendsto_arg_normalEndpointRatio_neg
  constructor
  · simpa only [PlaneChain.angle_append,PlaneChain.single_angle,sub_eq_add_neg,add_comm] using
      hsegPlus.add (hplus.mono_left nhdsWithin_le_nhds)
  · simpa only [PlaneChain.angle_append,PlaneChain.single_angle,add_comm] using
      hsegMinus.add (hminus.mono_left nhdsWithin_le_nhds)

end Swanepoel
