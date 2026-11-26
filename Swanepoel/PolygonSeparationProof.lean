module
public import Swanepoel.PolygonSeparationJump
@[expose] public section

noncomputable section
namespace Swanepoel
open Filter
open scoped Topology

theorem planeComplex_quarterTurn (u : Plane) :
    planeComplex (quarterTurn u)=planeComplex u*Complex.I := by
  apply Complex.ext <;> simp [planeComplex,quarterTurn]

def PennyGraph.normalProbe {n : ℕ} (G : PennyGraph n) (e : ContactEdge G) (s : ℝ) : Plane :=
  G.edgePoint e.val.1 e.val.2 (1/2)+s • quarterTurn (G.point e.val.2-G.point e.val.1)

theorem PennyGraph.continuous_normalProbe {n : ℕ} (G : PennyGraph n) (e : ContactEdge G) :
    Continuous (G.normalProbe e) := continuous_const.add (continuous_id.smul continuous_const)

theorem PennyGraph.segmentAngle_normalProbe {n : ℕ} (G : PennyGraph n) (e : ContactEdge G)
    (s : ℝ) : segmentAngle (G.point e.val.2) (G.point e.val.1) (G.normalProbe e s)=
      Complex.arg (normalEndpointRatio s) := by
  have hv : planeComplex (G.point e.val.2)-planeComplex (G.point e.val.1)≠0 := by
    apply sub_ne_zero.mpr
    intro hh
    exact e.property.2.ne (G.point_injective (planeComplex_injective hh)).symm
  have hnum : planeComplex (G.point e.val.1)-planeComplex (G.normalProbe e s)=
      ((-1/2 : ℂ)-(s : ℂ)*Complex.I)*
        (planeComplex (G.point e.val.2)-planeComplex (G.point e.val.1)) := by
    simp only [PennyGraph.normalProbe,PennyGraph.edgePoint,map_add,map_smul,
      planeComplex_quarterTurn,map_sub,Complex.real_smul]
    push_cast
    ring
  have hden : planeComplex (G.point e.val.2)-planeComplex (G.normalProbe e s)=
      ((1/2 : ℂ)-(s : ℂ)*Complex.I)*
        (planeComplex (G.point e.val.2)-planeComplex (G.point e.val.1)) := by
    simp only [PennyGraph.normalProbe,PennyGraph.edgePoint,map_add,map_smul,
      planeComplex_quarterTurn,map_sub,Complex.real_smul]
    push_cast
    ring
  unfold segmentAngle
  rw [hnum,hden,mul_div_mul_right _ _ hv]
  rfl

theorem PennyGraph.closingAngle_normal_limits {n : ℕ} (G : PennyGraph n) (e : ContactEdge G) :
    Tendsto (fun s : ℝ => segmentAngle (G.point e.val.2) (G.point e.val.1) (G.normalProbe e s))
        (𝓝[>] 0) (𝓝 (-Real.pi)) ∧
    Tendsto (fun s : ℝ => segmentAngle (G.point e.val.2) (G.point e.val.1) (G.normalProbe e (-s)))
        (𝓝[>] 0) (𝓝 Real.pi) := by
  simp only [G.segmentAngle_normalProbe]
  exact ⟨tendsto_arg_normalEndpointRatio_pos,tendsto_arg_normalEndpointRatio_neg⟩

theorem PennyGraph.separateInsertionSides_of_walk {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) (he : e∉S)
    (p : (G.contactGraph S).Walk e.val.1 e.val.2) : ¬G.SameInsertionSides S e := by
  intro hsame
  let m := G.edgePoint e.val.1 e.val.2 (1/2)
  let d := G.edgeClearance S e (1/2)
  have hd : 0<d := (G.edgeClearance_spec S e he (t := 1/2) (by norm_num) (by norm_num)).1
  have hu : ‖G.point e.val.2-G.point e.val.1‖=1 := by
    simpa only [← dist_eq_norm] using e.property.2.symm.2
  have hx := G.edgeSidePoint_mem_complement S e he true (t := 1/2) (by norm_num) (by norm_num)
  have hfixed := G.edge_sides_in_fixed_components S e he (t := 1/2) (by norm_num) (by norm_num)
  have heq (s : ℝ) (hs : 0<s) (hsd : s<d) :
      G.closedPathAngle p (G.normalProbe e s)=G.closedPathAngle p (G.normalProbe e (-s)) := by
    have hm := normal_offset_mem_halfBalls _ m hu hs
    have hb : Metric.ball m (2*s)⊆Metric.ball m (2*d) := Metric.ball_subset_ball (by linarith)
    have hL := hfixed.1 ⟨hb hm.1.1,hm.1.2⟩
    have hR := hfixed.2 ⟨hb hm.2.1,hm.2.2⟩
    change G.normalProbe e s∈_ at hL
    change G.normalProbe e (-s)∈_ at hR
    unfold PennyGraph.SameInsertionSides at hsame
    rw [← hsame] at hR
    exact (G.closedPathAngle_constant_on_component S e p hx hL).symm.trans
      (G.closedPathAngle_constant_on_component S e p hx hR)
  have hEq : (fun s : ℝ => G.closedPathAngle p (G.normalProbe e s)) =ᶠ[𝓝[>] 0]
      (fun s : ℝ => G.closedPathAngle p (G.normalProbe e (-s))) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hd)] with s hs hsd
    exact heq s hs hsd
  have hm : m∉G.subdrawing S :=
    Set.disjoint_left.mp (G.omitted_edge_disjoint_subdrawing S e he)
      ⟨1/2,⟨by norm_num,by norm_num⟩,rfl⟩
  have hpath := G.continuousAt_walkAngle p hm
  have hplus : Tendsto (fun s : ℝ => G.walkAngle p (G.normalProbe e s))
      (𝓝 0) (𝓝 (G.walkAngle p m)) := by
    simpa only [Function.comp_def,PennyGraph.normalProbe,zero_smul,add_zero,m] using
      (hpath.comp_of_eq ((G.continuous_normalProbe e).continuousAt (x := (0 : ℝ)))
        (by simp [PennyGraph.normalProbe,m])).tendsto
  have hminus : Tendsto (fun s : ℝ => G.walkAngle p (G.normalProbe e (-s)))
      (𝓝 0) (𝓝 (G.walkAngle p m)) := by
    simpa only [Function.comp_def,PennyGraph.normalProbe,neg_zero,zero_smul,add_zero,m] using
      (hpath.comp_of_eq (((G.continuous_normalProbe e).comp continuous_neg).continuousAt (x := (0 : ℝ)))
        (by simp [PennyGraph.normalProbe,m])).tendsto
  have hclosing := G.closingAngle_normal_limits e
  have hlimL : Tendsto (fun s : ℝ => G.closedPathAngle p (G.normalProbe e s))
      (𝓝[>] 0) (𝓝 (G.walkAngle p m-Real.pi)) := by
    simpa only [PennyGraph.closedPathAngle,sub_eq_add_neg] using
      (hplus.mono_left nhdsWithin_le_nhds).add hclosing.1
  have hlimR : Tendsto (fun s : ℝ => G.closedPathAngle p (G.normalProbe e (-s)))
      (𝓝[>] 0) (𝓝 (G.walkAngle p m+Real.pi)) := by
    exact (hminus.mono_left nhdsWithin_le_nhds).add hclosing.2
  have hcontr := tendsto_nhds_unique hlimL (hlimR.congr' hEq.symm)
  linarith [Real.pi_pos]

theorem PennyGraph.faceEuler_of_connected {n : ℕ} (G : PennyGraph n)
    (hc : G.graph.Connected) : G.FaceEuler := by
  apply G.faceEuler_of_cycle_separation hc
  intro S e he hr
  obtain ⟨p⟩ := hr
  exact G.separateInsertionSides_of_walk S e he p

theorem PennyGraph.euler_with_defects_of_connected {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (hc : G.graph.Connected) :
    (n : ℤ)-G.edgeCount+(Fintype.card (RhombusSet G)+G.faceDefectCount ht)=1 :=
  G.euler_with_defects ht (G.faceEuler_of_connected hc)

end Swanepoel
