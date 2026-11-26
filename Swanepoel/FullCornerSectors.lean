module
public import Swanepoel.VertexSectorClearance
public import Swanepoel.FaceBoundaryPermutation
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def fullClockwiseVertexSector (p u w : Plane) (r : ℝ) : Set Plane :=
  if cross2 u w<0 then clockwiseVertexSector p u w r else
  if cross2 u w=0 then rightHalfBall u p r else
    rightHalfBall u p r ∪ leftHalfBall w p r

theorem fullClockwiseVertexSector_subset_ball (p u w : Plane) (r : ℝ) :
    fullClockwiseVertexSector p u w r ⊆ Metric.ball p r := by
  unfold fullClockwiseVertexSector
  split_ifs
  · exact fun _ h => h.1.1
  · exact fun _ h => h.1
  · rintro z (h | h) <;> exact h.1

theorem unit_ray_right_halfBall_meets (p u : Plane) (hu : ‖u‖=1)
    {r ε : ℝ} (hr : 0<r) (hε : 0<ε) :
    ∃ z, z∈rightHalfBall u p r ∧
      z∈rightHalfBall u (p+(r/4) • u) ε := by
  let d := min (r/4) (ε/2)
  have hd : 0<d := lt_min (by positivity) (by positivity)
  have hdr : d≤r/4 := min_le_left _ _
  have hdε : 2*d≤ε := by have := min_le_right (r/4) (ε/2); dsimp [d]; linarith
  let q := p+(r/4) • u
  have hb := (normal_offset_mem_halfBalls u q hu hd).2
  refine ⟨q+(-d) • quarterTurn u,⟨?_,?_⟩,
    (Metric.ball_subset_ball hdε) hb.1,hb.2⟩
  · rw [Metric.mem_ball,dist_eq_norm,
      show q+(-d) • quarterTurn u-p=(r/4) • u+(-d) • quarterTurn u by dsimp [q]; abel]
    calc
      _ ≤ ‖(r/4) • u‖+‖(-d) • quarterTurn u‖ := norm_add_le _ _
      _ = r/4+d := by
        rw [norm_smul,norm_smul,quarterTurn_norm,hu,Real.norm_eq_abs,
          Real.norm_eq_abs,abs_of_pos (by positivity : 0<r/4),abs_neg,abs_of_pos hd]
        ring
      _ < r := by linarith
  · have hq : cross2 u q=cross2 u p := by
      simp only [q,cross2_add_right,cross2_smul_right,cross2_self,mul_zero,add_zero]
    change cross2 u (q+(-d) • quarterTurn u)<cross2 u p
    rw [← hq]
    exact hb.2

theorem unit_ray_left_halfBall_meets (p u : Plane) (hu : ‖u‖=1)
    {r ε : ℝ} (hr : 0<r) (hε : 0<ε) :
    ∃ z, z∈leftHalfBall u p r ∧
      z∈leftHalfBall u (p+(r/4) • u) ε := by
  let d := min (r/4) (ε/2)
  have hd : 0<d := lt_min (by positivity) (by positivity)
  have hdr : d≤r/4 := min_le_left _ _
  have hdε : 2*d≤ε := by have := min_le_right (r/4) (ε/2); dsimp [d]; linarith
  let q := p+(r/4) • u
  have hb := (normal_offset_mem_halfBalls u q hu hd).1
  refine ⟨q+d • quarterTurn u,⟨?_,?_⟩,
    (Metric.ball_subset_ball hdε) hb.1,hb.2⟩
  · rw [Metric.mem_ball,dist_eq_norm,
      show q+d • quarterTurn u-p=(r/4) • u+d • quarterTurn u by dsimp [q]; abel]
    calc
      _ ≤ ‖(r/4) • u‖+‖d • quarterTurn u‖ := norm_add_le _ _
      _ = r/4+d := by
        rw [norm_smul,norm_smul,quarterTurn_norm,hu,Real.norm_eq_abs,
          Real.norm_eq_abs,abs_of_pos (by positivity : 0<r/4),abs_of_pos hd]
        ring
      _ < r := by linarith
  · have hq : cross2 u q=cross2 u p := by
      simp only [q,cross2_add_right,cross2_smul_right,cross2_self,mul_zero,add_zero]
    change cross2 u p<cross2 u (q+d • quarterTurn u)
    rw [← hq]
    exact hb.2

theorem PennyGraph.right_half_corner_subset_face {n : ℕ} (G : PennyGraph n)
    (v a : Fin n) (hva : G.graph.Adj v a)
    (hno : ∀ c, G.graph.Adj v c → ¬ cross2 (G.point a-G.point v) (G.point c-G.point v)<0) :
    rightHalfBall (G.point a-G.point v) (G.point v) (1/2) ⊆
      (G.sourceFace ⟨(v,a),hva⟩).val := by
  let u := G.point a-G.point v
  let e : OrientedEdge G := ⟨(v,a),hva⟩
  have hu : ‖u‖=1 := by simpa only [u,← dist_eq_norm] using hva.symm.2
  have hclear : rightHalfBall u (G.point v) (1/2) ⊆ G.drawingᶜ := by
    intro z hz hdraw
    rcases (G.vertex_half_star v z hz.1).mp hdraw with rfl | ⟨c,hvc,t,ht,_,rfl⟩
    · exact (lt_irrefl _) (show cross2 u (G.point v)<cross2 u (G.point v) from hz.2)
    · apply hno c hvc
      have hc := hz.2
      change cross2 u (G.point v+t • (G.point c-G.point v))<cross2 u (G.point v) at hc
      rw [cross2_add_right,cross2_smul_right] at hc
      nlinarith
  obtain ⟨ε,hε,hεsub⟩ := G.right_face_halfBall_at e (t := 1/8) (by norm_num) (by norm_num)
  obtain ⟨z,hz,hze⟩ := unit_ray_right_halfBall_meets (G.point v) u hu
    (r := 1/2) (by norm_num) hε
  have hepoint : G.edgePoint e.val.1 e.val.2 (1/8)=G.point v+((1/2:ℝ)/4) • u := by
    dsimp [e,u,PennyGraph.edgePoint]
    module
  have hzF : z∈(G.sourceFace e).val := hεsub (by simpa only [hepoint,e,carriedVector,u] using hze)
  intro y hy
  have hc := (isPreconnected_rightHalfBall u (G.point v) (1/2)).subset_connectedComponentIn
    hz hclear hy
  rwa [← (G.sourceFace e).property.eq_component hzF] at hc

theorem PennyGraph.left_half_corner_subset_reverse_face {n : ℕ} (G : PennyGraph n)
    (v a : Fin n) (hva : G.graph.Adj v a)
    (hno : ∀ c, G.graph.Adj v c → ¬ 0<cross2 (G.point a-G.point v) (G.point c-G.point v)) :
    leftHalfBall (G.point a-G.point v) (G.point v) (1/2) ⊆
      (G.sourceFace (reverseEdge ⟨(v,a),hva⟩)).val := by
  let u := G.point a-G.point v
  let e : OrientedEdge G := ⟨(v,a),hva⟩
  have hu : ‖u‖=1 := by simpa only [u,← dist_eq_norm] using hva.symm.2
  have hclear : leftHalfBall u (G.point v) (1/2) ⊆ G.drawingᶜ := by
    intro z hz hdraw
    rcases (G.vertex_half_star v z hz.1).mp hdraw with rfl | ⟨c,hvc,t,ht,_,rfl⟩
    · exact (lt_irrefl _) (show cross2 u (G.point v)<cross2 u (G.point v) from hz.2)
    · apply hno c hvc
      have hc := hz.2
      change cross2 u (G.point v)<cross2 u (G.point v+t • (G.point c-G.point v)) at hc
      rw [cross2_add_right,cross2_smul_right] at hc
      nlinarith
  obtain ⟨ε,hε,hεsub⟩ := G.left_face_halfBall_at e (t := 1/8) (by norm_num) (by norm_num)
  obtain ⟨q,hq,hqe⟩ := unit_ray_left_halfBall_meets (G.point v) u hu
    (r := 1/2) (by norm_num) hε
  have hepoint : G.edgePoint e.val.1 e.val.2 (1/8)=G.point v+((1/2:ℝ)/4) • u := by
    dsimp [e,u,PennyGraph.edgePoint]
    module
  have hqF : q∈(G.sourceFace (reverseEdge e)).val :=
    hεsub (by simpa only [hepoint,e,carriedVector,u] using hqe)
  intro y hy
  have hc := (isPreconnected_leftHalfBall u (G.point v) (1/2)).subset_connectedComponentIn
    hq hclear hy
  rwa [← (G.sourceFace (reverseEdge e)).property.eq_component hqF] at hc

theorem PennyGraph.full_half_sector_subset_face {n : ℕ} (G : PennyGraph n)
    (v : Fin n) (a b : VertexRay G v)
    (hne : a≠b)
    (hgap : ∀ c : VertexRay G v,
      ¬ClockwiseRayBetween (G.vertexDirection v a) (G.vertexDirection v b) (G.vertexDirection v c)) :
    fullClockwiseVertexSector (G.point v) (G.vertexDirection v a) (G.vertexDirection v b) (1/2) ⊆
      (G.sourceFace ⟨(v,a.val),a.property⟩).val := by
  have hdir : G.vertexDirection v a≠G.vertexDirection v b :=
    fun h => hne (G.vertexDirection_injective v h)
  by_cases hc : cross2 (G.vertexDirection v a) (G.vertexDirection v b)<0
  · rw [fullClockwiseVertexSector,ite_eq_left hc]
    apply G.clockwise_half_sector_subset_face v a.val b.val a.property b.property hc
    intro c hvc hh
    apply hgap ⟨c,hvc⟩
    simp only [ClockwiseRayBetween,ite_eq_right hdir,ite_eq_left hc]
    simpa only [PennyGraph.vertexDirection] using hh
  have hnoRight : ∀ c, G.graph.Adj v c →
      ¬cross2 (G.vertexDirection v a) (G.point c-G.point v)<0 := by
    intro c hvc hh
    apply hgap ⟨c,hvc⟩
    by_cases hz : cross2 (G.vertexDirection v a) (G.vertexDirection v b)=0
    · simp only [ClockwiseRayBetween,ite_eq_right hdir,ite_eq_right hc,ite_eq_left hz]
      simpa only [PennyGraph.vertexDirection] using hh
    · simp only [ClockwiseRayBetween,ite_eq_right hdir,ite_eq_right hc,ite_eq_right hz]
      exact Or.inl hh
  have hright := G.right_half_corner_subset_face v a.val a.property hnoRight
  rw [fullClockwiseVertexSector,ite_eq_right hc]
  split_ifs with hz
  · exact hright
  · apply Set.union_subset hright
    have hnoLeft : ∀ c, G.graph.Adj v c →
        ¬ 0<cross2 (G.vertexDirection v b) (G.point c-G.point v) := by
      intro c hvc hh
      apply hgap ⟨c,hvc⟩
      simp only [ClockwiseRayBetween,ite_eq_right hdir,ite_eq_right hc,ite_eq_right hz]
      exact Or.inr hh
    have hleft := G.left_half_corner_subset_reverse_face v b.val b.property hnoLeft
    rw [← G.empty_clockwise_ray_face v a b hgap] at hleft
    exact hleft

theorem PennyGraph.vertexRayRotation_ne_self {n : ℕ} (G : PennyGraph n)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (v : Fin n) (a : VertexRay G v) : G.vertexRayRotation v a≠a := by
  intro heq
  obtain ⟨b,hb,hne⟩ := hdegree v a.val a.property
  have hempty := clockwiseRayPermutation_empty (G.vertexDirection v) (G.vertexDirection_norm v)
    (G.vertexDirection_injective v) a (⟨b,hb⟩ : VertexRay G v)
  change ¬ClockwiseRayBetween (G.vertexDirection v a)
    (G.vertexDirection v (G.vertexRayRotation v a)) (G.vertexDirection v ⟨b,hb⟩) at hempty
  rw [heq] at hempty
  apply hempty
  simp only [ClockwiseRayBetween,ite_true]
  intro h
  exact hne (congrArg Subtype.val (G.vertexDirection_injective v h))

theorem PennyGraph.rotation_half_sector_subset_face {n : ℕ} (G : PennyGraph n)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (v : Fin n) (a : VertexRay G v) :
    fullClockwiseVertexSector (G.point v) (G.vertexDirection v a)
      (G.vertexDirection v (G.vertexRayRotation v a)) (1/2) ⊆
      (G.sourceFace ⟨(v,a.val),a.property⟩).val :=
  G.full_half_sector_subset_face v a (G.vertexRayRotation v a)
    (G.vertexRayRotation_ne_self hdegree v a).symm
    (clockwiseRayPermutation_empty (G.vertexDirection v) (G.vertexDirection_norm v)
      (G.vertexDirection_injective v) a)

end Swanepoel
