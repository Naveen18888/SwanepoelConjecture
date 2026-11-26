module
public import Swanepoel.FaceBoundaryOrder
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem PennyGraph.nonincident_edge_clearance {n : ℕ} (G : PennyGraph n)
    (v a b : Fin n) (hab : G.graph.Adj a b) (hva : v≠a) (hvb : v≠b)
    {t : ℝ} (ht0 : 0≤t) (ht1 : t≤1) :
    Real.sqrt 3/2≤dist (G.edgePoint a b t) (G.point v) := by
  have hA := G.separated a v hva.symm
  have hB := G.separated b v hvb.symm
  have hAsq : 1≤‖G.point a-G.point v‖^2 := by
    rw [← dist_eq_norm]
    nlinarith [sq_nonneg (dist (G.point a) (G.point v)-1)]
  have hBsq : 1≤‖G.point b-G.point v‖^2 := by
    rw [← dist_eq_norm]
    nlinarith [sq_nonneg (dist (G.point b) (G.point v)-1)]
  have h1 := mul_le_mul_of_nonneg_left hAsq (sub_nonneg.mpr ht1)
  have h2 := mul_le_mul_of_nonneg_left hBsq ht0
  have hv := segment_variance (G.point a) (G.point b) (G.point v) (G.point v) t 0
  have hAB : ‖G.point a-G.point b‖=1 := by simpa only [dist_eq_norm] using hab.2
  simp only [sub_self,norm_zero,zero_pow (by decide : 2≠0),zero_mul,mul_zero,
    sub_zero,one_smul,zero_smul,add_zero,hAB,one_pow] at hv
  change _=‖G.edgePoint a b t-G.point v‖^2 at hv
  have hsq : (3/4:ℝ)≤dist (G.edgePoint a b t) (G.point v)^2 := by
    rw [dist_eq_norm]
    nlinarith [sq_nonneg (t-1/2)]
  have hsqrt := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have hnonneg := dist_nonneg (x := G.edgePoint a b t) (y := G.point v)
  have hsnonneg := Real.sqrt_nonneg (3:ℝ)
  nlinarith

theorem PennyGraph.vertex_half_star {n : ℕ} (G : PennyGraph n) (v : Fin n)
    (z : Plane) (hz : z∈Metric.ball (G.point v) (1/2:ℝ)) :
    z∈G.drawing ↔ z=G.point v ∨ ∃ w : Fin n, G.graph.Adj v w ∧
      ∃ t : ℝ, 0<t ∧ t<1/2 ∧ z=G.point v+t • (G.point w-G.point v) := by
  constructor
  · intro hdraw
    by_cases hzp : z=G.point v
    · exact Or.inl hzp
    right
    rcases hdraw with ⟨i,hi⟩ | he
    · have hiv : i≠v := by intro h; exact hzp (hi.symm.trans (congrArg G.point h))
      have hs := G.separated i v hiv
      rw [hi] at hs
      exact False.elim (by have := hz; change dist z (G.point v)<1/2 at this; linarith)
    obtain ⟨e,t,ht,heq⟩ := Set.mem_iUnion.mp he
    have incident : e.val.1=v ∨ e.val.2=v := by
      by_contra hn
      have hc := G.nonincident_edge_clearance v e.val.1 e.val.2 e.property
        (Ne.symm (not_or.mp hn).1) (Ne.symm (not_or.mp hn).2) ht.1 ht.2
      rw [heq] at hc
      have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
      have hsn := Real.sqrt_nonneg (3:ℝ)
      have hz' : dist z (G.point v)<1/2 := hz
      have hdist := dist_nonneg (x := z) (y := G.point v)
      nlinarith
    have ray (a b : Fin n) (hab : G.graph.Adj a b) (hav : a=v)
        (s : ℝ) (hs0 : 0≤s) (hpoint : G.edgePoint a b s=z) :
        ∃ w : Fin n, G.graph.Adj v w ∧ ∃ t : ℝ,
          0<t ∧ t<1/2 ∧ z=G.point v+t • (G.point w-G.point v) := by
      subst a
      have hrepr : z=G.point v+s • (G.point b-G.point v) := by
        rw [← hpoint]
        dsimp [PennyGraph.edgePoint]
        module
      have hspos : 0<s := by
        by_contra hn
        have hs : s=0 := le_antisymm (le_of_not_gt hn) hs0
        exact hzp (by simpa only [hs,zero_smul,add_zero] using hrepr)
      have hslt : s<1/2 := by
        have hd := G.edgePoint_dist_start v b hab hs0
        rw [hpoint] at hd
        exact hd ▸ hz
      exact ⟨b,hab,s,hspos,hslt,hrepr⟩
    rcases incident with h | h
    · exact ray _ _ e.property h t ht.1 heq
    · apply ray _ _ e.property.symm h (1-t) (by linarith [ht.2])
      rw [G.edgePoint_reverse]
      exact heq
  · rintro (rfl | ⟨w,hw,t,ht0,ht1,rfl⟩)
    · exact G.point_mem_drawing v
    · apply G.edgeTrace_subset_drawing v w hw
      refine ⟨t,⟨ht0.le,by linarith⟩,?_⟩
      dsimp [PennyGraph.edgePoint]
      module

theorem PennyGraph.clockwise_half_sector_subset_face {n : ℕ} (G : PennyGraph n)
    (v a b : Fin n) (hva : G.graph.Adj v a) (hvb : G.graph.Adj v b)
    (hc : cross2 (G.point a-G.point v) (G.point b-G.point v)<0)
    (hgap : ∀ c : Fin n, G.graph.Adj v c →
      ¬ (cross2 (G.point a-G.point v) (G.point c-G.point v)<0 ∧
        0<cross2 (G.point b-G.point v) (G.point c-G.point v))) :
    clockwiseVertexSector (G.point v) (G.point a-G.point v) (G.point b-G.point v) (1/2) ⊆
      (G.sourceFace ⟨(v,a),hva⟩).val := by
  let u := G.point a-G.point v
  let w := G.point b-G.point v
  let e : OrientedEdge G := ⟨(v,a),hva⟩
  have hu : ‖u‖=1 := by simpa only [u,← dist_eq_norm] using hva.symm.2
  have hw : ‖w‖=1 := by simpa only [w,← dist_eq_norm] using hvb.symm.2
  have hsect : clockwiseVertexSector (G.point v) u w (1/2) ⊆ G.drawingᶜ := by
    intro z hz hdraw
    rcases (G.vertex_half_star v z hz.1.1).mp hdraw with rfl | ⟨c,hvc,t,ht0,_,rfl⟩
    · exact (lt_irrefl (cross2 u (G.point v))) hz.1.2
    · apply hgap c hvc
      have hr := hz.1.2
      have hl := hz.2.2
      change cross2 u (G.point v+t • (G.point c-G.point v))<cross2 u (G.point v) at hr
      change cross2 w (G.point v)<cross2 w (G.point v+t • (G.point c-G.point v)) at hl
      simp only [cross2_add_right,cross2_smul_right] at hr hl
      exact ⟨by nlinarith,by nlinarith⟩
  obtain ⟨ε,hε,hεsub⟩ := G.right_face_halfBall_at e (t := 1/8) (by norm_num) (by norm_num)
  obtain ⟨z,hz,hzr⟩ := clockwiseVertexSector_meets_right (G.point v) u w hu hw hc
    (r := 1/2) (by norm_num) hε
  have hepoint : G.edgePoint e.val.1 e.val.2 (1/8)=G.point v+((1/2:ℝ)/4) • u := by
    dsimp [e,u,PennyGraph.edgePoint]
    module
  have hze : z∈(G.sourceFace e).val := hεsub (by simpa only [hepoint,e,carriedVector,u] using hzr)
  intro y hy
  have hcomp := (clockwiseVertexSector_preconnected (G.point v) u w (1/2)).subset_connectedComponentIn
    hz hsect hy
  rwa [← (G.sourceFace e).property.eq_component hze] at hcomp

theorem PennyGraph.disjoint_half_sectors {n : ℕ} (G : PennyGraph n)
    (v w : Fin n) (hvw : v≠w) (u₁ u₂ w₁ w₂ : Plane) :
    Disjoint (clockwiseVertexSector (G.point v) u₁ u₂ (1/2))
      (clockwiseVertexSector (G.point w) w₁ w₂ (1/2)) := by
  apply Set.disjoint_left.mpr
  intro z hzv hzw
  have hv : dist z (G.point v)<1/2 := hzv.1.1
  have hw : dist z (G.point w)<1/2 := hzw.1.1
  have hs := G.separated v w hvw
  have htri := dist_triangle (G.point v) z (G.point w)
  rw [dist_comm (G.point v) z] at htri
  linarith

end Swanepoel
