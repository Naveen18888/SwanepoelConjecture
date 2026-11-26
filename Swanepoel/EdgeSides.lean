module
public import Swanepoel.EdgeNeighbourhood
public import Mathlib.Topology.MetricSpace.HausdorffDistance
@[expose] public section

noncomputable section
namespace Swanepoel

def PennyGraph.edgeClearance {n : ℕ} (G : PennyGraph n) (S : Finset (ContactEdge G))
    (e : ContactEdge G) (t : ℝ) : ℝ :=
  min t (min (1-t) (Metric.infDist (G.edgePoint e.val.1 e.val.2 t) (G.subdrawing S)))/4

theorem PennyGraph.continuous_edgeClearance {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) : Continuous (G.edgeClearance S e) :=
  (continuous_id.min ((continuous_const.sub continuous_id).min
    ((Metric.continuous_infDist_pt (G.subdrawing S)).comp (G.continuous_edgePoint _ _)))).div_const 4

theorem PennyGraph.edgeClearance_spec {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) (he : e∉S)
    {t : ℝ} (ht0 : 0<t) (ht1 : t<1) :
    0<G.edgeClearance S e t ∧ 2*G.edgeClearance S e t<t ∧ 2*G.edgeClearance S e t<1-t ∧
      2*G.edgeClearance S e t<Metric.infDist (G.edgePoint e.val.1 e.val.2 t) (G.subdrawing S) := by
  have hne : (G.subdrawing S).Nonempty := ⟨G.point e.val.1,Or.inl ⟨e.val.1,rfl⟩⟩
  have hp : G.edgePoint e.val.1 e.val.2 t∉G.subdrawing S :=
    Set.disjoint_left.mp (G.omitted_edge_disjoint_subdrawing S e he) ⟨t,⟨ht0,ht1⟩,rfl⟩
  have hd := ((G.isCompact_subdrawing S).isClosed.notMem_iff_infDist_pos hne).mp hp
  have hpos := lt_min ht0 (lt_min (by linarith : 0<1-t) hd)
  have hle0 := min_le_left t (min (1-t) (Metric.infDist (G.edgePoint e.val.1 e.val.2 t) (G.subdrawing S)))
  have hle1 := (min_le_right t (min (1-t) (Metric.infDist (G.edgePoint e.val.1 e.val.2 t) (G.subdrawing S)))).trans
    (min_le_left (1-t) _)
  have hle2 := (min_le_right t (min (1-t) (Metric.infDist (G.edgePoint e.val.1 e.val.2 t) (G.subdrawing S)))).trans
    (min_le_right (1-t) _)
  dsimp [PennyGraph.edgeClearance]
  exact ⟨by positivity,by linarith,by linarith,by linarith⟩

def PennyGraph.edgeSidePoint {n : ℕ} (G : PennyGraph n) (S : Finset (ContactEdge G))
    (e : ContactEdge G) (left : Bool) (t : ℝ) : Plane :=
  G.edgePoint e.val.1 e.val.2 t+
    (if left then G.edgeClearance S e t else -G.edgeClearance S e t) •
      quarterTurn (G.point e.val.2-G.point e.val.1)

theorem PennyGraph.continuous_edgeSidePoint {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) (left : Bool) :
    Continuous (G.edgeSidePoint S e left) := by
  cases left
  · exact (G.continuous_edgePoint _ _).add ((G.continuous_edgeClearance S e).neg.smul continuous_const)
  · exact (G.continuous_edgePoint _ _).add ((G.continuous_edgeClearance S e).smul continuous_const)

theorem normal_offset_mem_halfBalls (u p : Plane) (hu : ‖u‖=1) {d : ℝ} (hd : 0<d) :
    p+d • quarterTurn u∈leftHalfBall u p (2*d) ∧
    p+(-d) • quarterTurn u∈rightHalfBall u p (2*d) := by
  have hn : ‖quarterTurn u‖=1 := by rw [quarterTurn_norm,hu]
  have hc : cross2 u (quarterTurn u)=1 := by rw [cross_quarterTurn,hu]; norm_num
  constructor
  · refine ⟨?_,?_⟩
    · rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,hn,Real.norm_eq_abs,abs_of_pos hd,mul_one]
      linarith
    · change cross2 u p<cross2 u (p+d • quarterTurn u)
      rw [cross2_add_right,cross2_smul_right,hc]
      linarith
  · refine ⟨?_,?_⟩
    · rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,hn,Real.norm_eq_abs,
        abs_neg,abs_of_pos hd,mul_one]
      linarith
    · change cross2 u (p+(-d) • quarterTurn u)<cross2 u p
      rw [cross2_add_right,cross2_smul_right,hc]
      linarith

theorem PennyGraph.edgeClearance_ball_complement {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) (he : e∉S)
    {t : ℝ} (ht0 : 0<t) (ht1 : t<1) :
    Metric.ball (G.edgePoint e.val.1 e.val.2 t) (2*G.edgeClearance S e t) ∩
        (G.subdrawing (insert e S))ᶜ=
      leftHalfBall (G.point e.val.2-G.point e.val.1) (G.edgePoint e.val.1 e.val.2 t)
          (2*G.edgeClearance S e t) ∪
      rightHalfBall (G.point e.val.2-G.point e.val.1) (G.edgePoint e.val.1 e.val.2 t)
          (2*G.edgeClearance S e t) := by
  have hspec := G.edgeClearance_spec S e he ht0 ht1
  exact G.insert_edge_ball_complement S e hspec.2.1 hspec.2.2.1
    ((Metric.ball_subset_ball hspec.2.2.2.le).trans Metric.ball_infDist_subset_compl)

theorem PennyGraph.edgeSidePoint_mem_complement {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) (he : e∉S) (left : Bool)
    {t : ℝ} (ht0 : 0<t) (ht1 : t<1) :
    G.edgeSidePoint S e left t∈(G.subdrawing (insert e S))ᶜ := by
  have hspec := G.edgeClearance_spec S e he ht0 ht1
  have hu : ‖G.point e.val.2-G.point e.val.1‖=1 := by
    simpa only [← dist_eq_norm] using e.property.2.symm.2
  have hmem := normal_offset_mem_halfBalls _ (G.edgePoint e.val.1 e.val.2 t) hu hspec.1
  have heq := G.edgeClearance_ball_complement S e he ht0 ht1
  have hU : leftHalfBall (G.point e.val.2-G.point e.val.1) (G.edgePoint e.val.1 e.val.2 t)
        (2*G.edgeClearance S e t) ∪
      rightHalfBall (G.point e.val.2-G.point e.val.1) (G.edgePoint e.val.1 e.val.2 t)
        (2*G.edgeClearance S e t) ⊆ (G.subdrawing (insert e S))ᶜ := by
    rw [← heq]
    exact Set.inter_subset_right
  cases left
  · exact hU (Or.inr hmem.2)
  · exact hU (Or.inl hmem.1)

theorem PennyGraph.edgeSidePoint_in_fixed_component {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) (he : e∉S) (left : Bool)
    {t : ℝ} (ht0 : 0<t) (ht1 : t<1) :
    G.edgeSidePoint S e left t∈connectedComponentIn (G.subdrawing (insert e S))ᶜ
      (G.edgeSidePoint S e left (1/2)) := by
  have hpre : IsPreconnected (G.edgeSidePoint S e left '' Set.Ioo (0 : ℝ) 1) :=
    isPreconnected_Ioo.image _ (G.continuous_edgeSidePoint S e left).continuousOn
  apply hpre.subset_connectedComponentIn (by
    exact ⟨1/2,⟨by norm_num,by norm_num⟩,rfl⟩) ?_ ⟨t,⟨ht0,ht1⟩,rfl⟩
  rintro z ⟨s,⟨hs0,hs1⟩,rfl⟩
  exact G.edgeSidePoint_mem_complement S e he left hs0 hs1

theorem PennyGraph.edge_sides_in_fixed_components {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) (he : e∉S)
    {t : ℝ} (ht0 : 0<t) (ht1 : t<1) :
    (leftHalfBall (G.point e.val.2-G.point e.val.1) (G.edgePoint e.val.1 e.val.2 t)
        (2*G.edgeClearance S e t) ⊆
      connectedComponentIn (G.subdrawing (insert e S))ᶜ (G.edgeSidePoint S e true (1/2))) ∧
    (rightHalfBall (G.point e.val.2-G.point e.val.1) (G.edgePoint e.val.1 e.val.2 t)
        (2*G.edgeClearance S e t) ⊆
      connectedComponentIn (G.subdrawing (insert e S))ᶜ (G.edgeSidePoint S e false (1/2))) := by
  have hd := (G.edgeClearance_spec S e he ht0 ht1).1
  have hu : ‖G.point e.val.2-G.point e.val.1‖=1 := by
    simpa only [← dist_eq_norm] using e.property.2.symm.2
  have hmem := normal_offset_mem_halfBalls _ (G.edgePoint e.val.1 e.val.2 t) hu hd
  have heq := G.edgeClearance_ball_complement S e he ht0 ht1
  have hU : leftHalfBall (G.point e.val.2-G.point e.val.1) (G.edgePoint e.val.1 e.val.2 t)
        (2*G.edgeClearance S e t) ∪
      rightHalfBall (G.point e.val.2-G.point e.val.1) (G.edgePoint e.val.1 e.val.2 t)
        (2*G.edgeClearance S e t) ⊆ (G.subdrawing (insert e S))ᶜ := by
    rw [← heq]
    exact Set.inter_subset_right
  constructor
  · have hsub : leftHalfBall (G.point e.val.2-G.point e.val.1) (G.edgePoint e.val.1 e.val.2 t)
          (2*G.edgeClearance S e t)⊆(G.subdrawing (insert e S))ᶜ := by
      exact fun _ hz => hU (Or.inl hz)
    intro z hz
    have hp := G.edgeSidePoint_in_fixed_component S e he true ht0 ht1
    rw [connectedComponentIn_eq hp]
    exact (isPreconnected_leftHalfBall _ _ _).subset_connectedComponentIn hmem.1 hsub hz
  · have hsub : rightHalfBall (G.point e.val.2-G.point e.val.1) (G.edgePoint e.val.1 e.val.2 t)
          (2*G.edgeClearance S e t)⊆(G.subdrawing (insert e S))ᶜ := by
      exact fun _ hz => hU (Or.inr hz)
    intro z hz
    have hp := G.edgeSidePoint_in_fixed_component S e he false ht0 ht1
    rw [connectedComponentIn_eq hp]
    exact (isPreconnected_rightHalfBall _ _ _).subset_connectedComponentIn hmem.2 hsub hz

end Swanepoel
