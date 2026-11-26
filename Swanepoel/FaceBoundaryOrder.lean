module
public import Swanepoel.FacePortIncidence
public import Swanepoel.EulerLeaf
@[expose] public section

noncomputable section
namespace Swanepoel
open Set Metric
attribute [local instance] Classical.propDecidable

theorem PennyGraph.vertex_local_star {n : ℕ} (G : PennyGraph n) (v : Fin n) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ z ∈ Metric.ball (G.point v) r,
      (z ∈ G.drawing ↔ z = G.point v ∨ ∃ w : Fin n, G.graph.Adj v w ∧
        ∃ t : ℝ, 0 < t ∧ t < r ∧ z = G.point v+t • (G.point w-G.point v)) := by
  let S : Finset (ContactEdge G) := Finset.univ.filter
    (fun e => e.val.1 ≠ v ∧ e.val.2 ≠ v)
  obtain ⟨r,hr,hr1,hfree⟩ := G.isolated_vertex_free_ball S v
    (fun e he => (Finset.mem_filter.mp he).2)
  refine ⟨r,hr,hr1,?_⟩
  intro z hz
  constructor
  · intro hdraw
    by_cases hzp : z = G.point v
    · exact Or.inl hzp
    right
    rw [← G.subdrawing_univ] at hdraw
    rcases hdraw with hp | he
    · exact False.elim (hzp (hfree z hz (Or.inl hp)))
    obtain ⟨e,he⟩ := Set.mem_iUnion.mp he
    obtain ⟨_,t,⟨ht0,ht1⟩,heq⟩ := Set.mem_iUnion.mp he
    have incident : e.val.1 = v ∨ e.val.2 = v := by
      by_contra hn
      have hS : e ∈ S := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,not_or.mp hn⟩
      exact hzp (hfree z hz (Or.inr (Set.mem_iUnion.mpr ⟨e,
        Set.mem_iUnion.mpr ⟨hS,t,⟨ht0,ht1⟩,heq⟩⟩)))
    have ray (a b : Fin n) (hab : G.graph.Adj a b) (hav : a = v)
        (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hpoint : G.edgePoint a b s = z) :
        ∃ w : Fin n, G.graph.Adj v w ∧ ∃ t : ℝ,
          0 < t ∧ t < r ∧ z = G.point v+t • (G.point w-G.point v) := by
      subst a
      have hrepr : z = G.point v+s • (G.point b-G.point v) := by
        rw [← hpoint]
        dsimp [PennyGraph.edgePoint]
        module
      have hspos : 0 < s := by
        by_contra hn
        have hsz : s = 0 := le_antisymm (le_of_not_gt hn) hs0
        exact hzp (by simpa only [hsz,zero_smul,add_zero] using hrepr)
      have hnorm : ‖G.point b-G.point v‖ = 1 := by
        simpa only [← dist_eq_norm] using hab.symm.2
      have hslt : s < r := by
        rw [Metric.mem_ball, hrepr, dist_eq_norm, add_sub_cancel_left,
          norm_smul, hnorm, Real.norm_eq_abs, abs_of_pos hspos, mul_one] at hz
        exact hz
      exact ⟨b,hab,s,hspos,hslt,hrepr⟩
    rcases incident with h | h
    · exact ray _ _ e.property.2 h t ht0 ht1 heq
    · apply ray _ _ e.property.2.symm h (1-t) (by linarith) (by linarith)
      rw [G.edgePoint_reverse]
      convert heq using 1
  · rintro (rfl | ⟨w,hw,t,ht0,htr,rfl⟩)
    · exact G.point_mem_drawing v
    · apply G.edgeTrace_subset_drawing v w hw
      refine ⟨t,⟨ht0.le,le_trans htr.le hr1⟩,?_⟩
      dsimp [PennyGraph.edgePoint]
      module

theorem PennyGraph.right_face_halfBall_at {n : ℕ} (G : PennyGraph n)
    (e : OrientedEdge G) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ r : ℝ, 0 < r ∧ rightHalfBall (carriedVector e)
      (G.edgePoint e.val.1 e.val.2 t) r ⊆ (G.sourceFace e).val := by
  let f := physicalEdge e
  let S := (Finset.univ : Finset (ContactEdge G)).erase f
  have hf : f ∉ S := Finset.notMem_erase _ _
  have hdrawing : G.subdrawing (insert f S) = G.drawing := by
    simp only [S,Finset.insert_erase (Finset.mem_univ _),G.subdrawing_univ]
  by_cases h : e.val.1 < e.val.2
  · have hfval : f.val = e.val := by simp [f,physicalEdge,h]
    have heq : f.forwardEdge = e := Subtype.ext hfval
    have hδ := (G.edgeClearance_spec S f hf ht0 ht1).1
    have hsides := (G.edge_sides_in_fixed_components S f hf ht0 ht1).2
    rw [hdrawing, G.contact_right_component_eq_sourceFace f, heq] at hsides
    refine ⟨2*G.edgeClearance S f t,by positivity,?_⟩
    simpa only [hfval,carriedVector] using hsides
  · have hfval : f.val = (e.val.2,e.val.1) := by simp [f,physicalEdge,h]
    have heq : reverseEdge f.forwardEdge = e := by
      apply Subtype.ext
      simp only [reverseEdge,ContactEdge.forwardEdge,hfval]
    have hδ := (G.edgeClearance_spec S f hf (show 0<1-t by linarith)
      (show 1-t<1 by linarith)).1
    have hsides := (G.edge_sides_in_fixed_components S f hf
      (show 0<1-t by linarith) (show 1-t<1 by linarith)).1
    rw [hdrawing, G.contact_left_component_eq_sourceFace f, heq] at hsides
    have hpoint : G.edgePoint f.val.1 f.val.2 (1-t) =
        G.edgePoint e.val.1 e.val.2 t := by
      rw [hfval,G.edgePoint_reverse]
    have hvec : G.point f.val.2-G.point f.val.1 = -carriedVector e := by
      simp only [hfval,carriedVector]
      abel
    refine ⟨2*G.edgeClearance S f (1-t),by positivity,?_⟩
    simpa only [hpoint,hvec,leftHalfBall_neg] using hsides

theorem PennyGraph.left_face_halfBall_at {n : ℕ} (G : PennyGraph n)
    (e : OrientedEdge G) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ r : ℝ, 0 < r ∧ leftHalfBall (carriedVector e)
      (G.edgePoint e.val.1 e.val.2 t) r ⊆ (G.sourceFace (reverseEdge e)).val := by
  obtain ⟨r,hr,hsub⟩ := G.right_face_halfBall_at (reverseEdge e)
    (show 0<1-t by linarith) (show 1-t<1 by linarith)
  have hpoint : G.edgePoint (reverseEdge e).val.1 (reverseEdge e).val.2 (1-t) =
      G.edgePoint e.val.1 e.val.2 t := by
    simp only [reverseEdge]
    rw [G.edgePoint_reverse]
  refine ⟨r,hr,?_⟩
  simpa only [hpoint,reverseEdge_vector,rightHalfBall,leftHalfBall,cross2_neg_left,
    neg_lt_neg_iff] using hsub

def clockwiseVertexSector (p u w : Plane) (r : ℝ) : Set Plane :=
  rightHalfBall u p r ∩ leftHalfBall w p r

theorem clockwiseVertexSector_preconnected (p u w : Plane) (r : ℝ) :
    IsPreconnected (clockwiseVertexSector p u w r) := by
  exact (((convex_ball p r).inter
    ((convex_Iio (cross2 u p)).linear_preimage (crossLinear u))).inter
    ((convex_ball p r).inter
      ((convex_Ioi (cross2 w p)).linear_preimage (crossLinear w)))).isPreconnected

private theorem fbo_cross_swap (u w : Plane) : cross2 w u = -cross2 u w := by
  unfold cross2
  ring

theorem clockwiseVertexSector_combination (p u w : Plane) (hu : ‖u‖=1) (hw : ‖w‖=1)
    (hc : cross2 u w < 0) {r a b : ℝ} (ha : 0<a) (hb : 0<b) (hab : a+b<r) :
    p+a • u+b • w ∈ clockwiseVertexSector p u w r := by
  have hdist : dist (p+a • u+b • w) p ≤ a+b := by
    rw [dist_eq_norm,show p+a • u+b • w-p=a • u+b • w by abel]
    exact (norm_add_le _ _).trans_eq (by
      rw [norm_smul,norm_smul,hu,hw,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_pos ha,abs_of_pos hb,mul_one,mul_one])
  have hball : p+a • u+b • w ∈ Metric.ball p r := hdist.trans_lt hab
  have hright : cross2 u (p+a • u+b • w) < cross2 u p := by
    simp only [cross2_add_right,cross2_smul_right,cross2_self,mul_zero,add_zero]
    exact add_lt_of_neg_right _ (mul_neg_of_pos_of_neg hb hc)
  have hleft : cross2 w p < cross2 w (p+a • u+b • w) := by
    simp only [cross2_add_right,cross2_smul_right,cross2_self,mul_zero,add_zero,
      fbo_cross_swap u w]
    exact lt_add_of_pos_right _ (mul_pos ha (neg_pos.mpr hc))
  exact ⟨⟨hball,hright⟩,hball,hleft⟩

theorem clockwiseVertexSector_meets_right (p u w : Plane) (hu : ‖u‖=1) (hw : ‖w‖=1)
    (hc : cross2 u w<0) {r ε : ℝ} (hr : 0<r) (hε : 0<ε) :
    ∃ z, z∈clockwiseVertexSector p u w r ∧
      z∈rightHalfBall u (p+(r/4) • u) ε := by
  let b := min (r/4) (ε/2)
  have hb : 0<b := lt_min (by positivity) (by positivity)
  have hbr : b ≤ r/4 := min_le_left _ _
  have hbε : b ≤ ε/2 := min_le_right _ _
  let z := p+(r/4) • u+b • w
  refine ⟨z,clockwiseVertexSector_combination p u w hu hw hc (by positivity) hb
    (by linarith),?_,?_⟩
  · have hdist : dist z (p+(r/4) • u) = b := by
      rw [dist_eq_norm]
      change ‖(p+(r/4) • u+b • w)-(p+(r/4) • u)‖=b
      rw [add_sub_cancel_left,norm_smul,hw,Real.norm_eq_abs,abs_of_pos hb,mul_one]
    exact hdist.trans_lt (by linarith)
  · change cross2 u z < cross2 u (p+(r/4) • u)
    dsimp [z]
    rw [cross2_add_right,cross2_smul_right]
    exact add_lt_of_neg_right _ (mul_neg_of_pos_of_neg hb hc)

theorem clockwiseVertexSector_meets_left (p u w : Plane) (hu : ‖u‖=1) (hw : ‖w‖=1)
    (hc : cross2 u w<0) {r ε : ℝ} (hr : 0<r) (hε : 0<ε) :
    ∃ z, z∈clockwiseVertexSector p u w r ∧
      z∈leftHalfBall w (p+(r/4) • w) ε := by
  let a := min (r/4) (ε/2)
  have ha : 0<a := lt_min (by positivity) (by positivity)
  have har : a ≤ r/4 := min_le_left _ _
  have haε : a ≤ ε/2 := min_le_right _ _
  let z := p+a • u+(r/4) • w
  refine ⟨z,clockwiseVertexSector_combination p u w hu hw hc ha (by positivity)
    (by linarith),?_,?_⟩
  · have hdist : dist z (p+(r/4) • w) = a := by
      rw [dist_eq_norm,show z-(p+(r/4) • w)=a • u by dsimp [z]; abel]
      rw [norm_smul,hu,Real.norm_eq_abs,abs_of_pos ha,mul_one]
    exact hdist.trans_lt (by linarith)
  · change cross2 w (p+(r/4) • w) < cross2 w z
    dsimp [z]
    simp only [cross2_add_right,cross2_smul_right,cross2_self,mul_zero,add_zero,
      fbo_cross_swap u w]
    exact lt_add_of_pos_right _ (mul_pos ha (neg_pos.mpr hc))

theorem PennyGraph.empty_clockwise_sector_face {n : ℕ} (G : PennyGraph n)
    (v a b : Fin n) (hva : G.graph.Adj v a) (hvb : G.graph.Adj v b)
    (hcross : cross2 (G.point a-G.point v) (G.point b-G.point v)<0)
    (hgap : ∀ c : Fin n, G.graph.Adj v c →
      ¬ (cross2 (G.point a-G.point v) (G.point c-G.point v)<0 ∧
        0<cross2 (G.point b-G.point v) (G.point c-G.point v))) :
    G.sourceFace ⟨(v,a),hva⟩ = G.sourceFace (reverseEdge ⟨(v,b),hvb⟩) := by
  let u := G.point a-G.point v
  let w := G.point b-G.point v
  let e : OrientedEdge G := ⟨(v,a),hva⟩
  let f : OrientedEdge G := ⟨(v,b),hvb⟩
  have hu : ‖u‖=1 := by simpa only [u,← dist_eq_norm] using hva.symm.2
  have hw : ‖w‖=1 := by simpa only [w,← dist_eq_norm] using hvb.symm.2
  obtain ⟨r,hr,hr1,hstar⟩ := G.vertex_local_star v
  have hsect : clockwiseVertexSector (G.point v) u w r ⊆ G.drawingᶜ := by
    intro z hz hdraw
    have hzstar := (hstar z hz.1.1).mp hdraw
    rcases hzstar with rfl | ⟨c,hvc,t,ht0,_,rfl⟩
    · exact (lt_irrefl (cross2 u (G.point v)))
        (show cross2 u (G.point v)<cross2 u (G.point v) from hz.1.2)
    · apply hgap c hvc
      have hright := hz.1.2
      have hleft := hz.2.2
      change cross2 u (G.point v+t • (G.point c-G.point v))<cross2 u (G.point v) at hright
      change cross2 w (G.point v)<cross2 w (G.point v+t • (G.point c-G.point v)) at hleft
      simp only [cross2_add_right,cross2_smul_right] at hright hleft
      exact ⟨by nlinarith,by nlinarith⟩
  have hs0 : 0<r/4 := by positivity
  have hs1 : r/4<1 := by linarith
  obtain ⟨ε,hε,hεsub⟩ := G.right_face_halfBall_at e hs0 hs1
  obtain ⟨δ,hδ,hδsub⟩ := G.left_face_halfBall_at f hs0 hs1
  have hepoint : G.edgePoint e.val.1 e.val.2 (r/4) = G.point v+(r/4) • u := by
    dsimp [e,u,PennyGraph.edgePoint]
    module
  have hfpoint : G.edgePoint f.val.1 f.val.2 (r/4) = G.point v+(r/4) • w := by
    dsimp [f,w,PennyGraph.edgePoint]
    module
  obtain ⟨z,hz,hzright⟩ := clockwiseVertexSector_meets_right (G.point v) u w hu hw hcross hr hε
  obtain ⟨y,hy,hyleft⟩ := clockwiseVertexSector_meets_left (G.point v) u w hu hw hcross hr hδ
  have hze : z ∈ (G.sourceFace e).val := hεsub (by simpa only [hepoint,e,carriedVector,u] using hzright)
  have hyf : y ∈ (G.sourceFace (reverseEdge f)).val :=
    hδsub (by simpa only [hfpoint,f,carriedVector,w] using hyleft)
  have hsame := (clockwiseVertexSector_preconnected (G.point v) u w r).subset_connectedComponentIn
    hz hsect hy
  apply Subtype.ext
  exact ((G.sourceFace e).property.eq_component hze).trans
    ((connectedComponentIn_eq hsame).trans ((G.sourceFace (reverseEdge f)).property.eq_component hyf).symm)

theorem cross2_in_unit_frame (u x y : Plane) (hu : ‖u‖=1) :
    cross2 x y = inner ℝ u x*cross2 u y-cross2 u x*inner ℝ u y := by
  have hcross : cross2 u (quarterTurn u)=1 := by rw [cross_quarterTurn,hu]; norm_num
  have hreverse : cross2 (quarterTurn u) u = -1 := by rw [fbo_cross_swap,hcross]
  calc
    _ = cross2 (inner ℝ u x • u+cross2 u x • quarterTurn u)
        (inner ℝ u y • u+cross2 u y • quarterTurn u) := by
          rw [← unit_direction_decomposition u x hu,← unit_direction_decomposition u y hu]
    _ = _ := by
      simp only [cross2_add_left,cross2_add_right,cross2_smul_left,cross2_smul_right,
        cross2_self,hcross,hreverse]
      ring

theorem PennyGraph.clockwise_successor_in_right_halfPlane {n : ℕ} (G : PennyGraph n)
    (v a : Fin n) (hva : G.graph.Adj v a)
    (hright : ∃ b : Fin n, G.graph.Adj v b ∧
      cross2 (G.point a-G.point v) (G.point b-G.point v)<0) :
    ∃ b : Fin n, ∃ hvb : G.graph.Adj v b,
      cross2 (G.point a-G.point v) (G.point b-G.point v)<0 ∧
      (∀ c : Fin n, G.graph.Adj v c →
        ¬ (cross2 (G.point a-G.point v) (G.point c-G.point v)<0 ∧
          0<cross2 (G.point b-G.point v) (G.point c-G.point v))) ∧
      G.sourceFace ⟨(v,a),hva⟩ = G.sourceFace (reverseEdge ⟨(v,b),hvb⟩) := by
  let u := G.point a-G.point v
  let direction (c : Fin n) := G.point c-G.point v
  let N : Finset (Fin n) := Finset.univ.filter
    (fun c => G.graph.Adj v c ∧ cross2 u (direction c)<0)
  have hN : N.Nonempty := by
    obtain ⟨b,hb,hcross⟩ := hright
    exact ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb,hcross⟩⟩
  let slope (c : Fin n) := inner ℝ u (direction c)/(-cross2 u (direction c))
  obtain ⟨b,hb,hmax⟩ := N.exists_max_image slope hN
  have hb' := (Finset.mem_filter.mp hb).2
  have hu : ‖u‖=1 := by simpa only [u,← dist_eq_norm] using hva.symm.2
  have hgap : ∀ c : Fin n, G.graph.Adj v c →
      ¬ (cross2 u (direction c)<0 ∧ 0<cross2 (direction b) (direction c)) := by
    intro c hvc hc
    have hcN : c∈N := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvc,hc.1⟩
    have hbound := hmax c hcN
    have hid := cross2_in_unit_frame u (direction b) (direction c) hu
    have hlt : slope b<slope c := by
      apply (div_lt_div_iff₀ (neg_pos.mpr hb'.2) (neg_pos.mpr hc.1)).mpr
      nlinarith [hc.2]
    exact (not_lt_of_ge hbound) hlt
  refine ⟨b,hb'.1,hb'.2,hgap,?_⟩
  exact G.empty_clockwise_sector_face v a b hva hb'.1 hb'.2 hgap

private theorem unit_ray_halfBall_meets (p u : Plane) (hu : ‖u‖=1)
    {r ε : ℝ} (hr : 0<r) (hε : 0<ε) :
    (∃ z, z∈rightHalfBall u p r ∧ z∈rightHalfBall u (p+(r/4) • u) ε) ∧
    (∃ z, z∈leftHalfBall u p r ∧ z∈leftHalfBall u (p+(r/4) • u) ε) := by
  let d := min (r/4) (ε/2)
  have hd : 0<d := lt_min (by positivity) (by positivity)
  have hdr : d≤r/4 := min_le_left _ _
  have hdε : 2*d≤ε := by have := min_le_right (r/4) (ε/2); dsimp [d]; linarith
  let q := p+(r/4) • u
  have hqcross : cross2 u q = cross2 u p := by
    dsimp [q]
    rw [cross2_add_right,cross2_smul_right,cross2_self,mul_zero,add_zero]
  have hballs := normal_offset_mem_halfBalls u q hu hd
  have hball (s : ℝ) (hs : |s|=d) : q+s • quarterTurn u ∈ Metric.ball p r := by
    rw [Metric.mem_ball,dist_eq_norm,
      show q+s • quarterTurn u-p=(r/4) • u+s • quarterTurn u by dsimp [q]; abel]
    calc
      _ ≤ ‖(r/4) • u‖+‖s • quarterTurn u‖ := norm_add_le _ _
      _ = r/4+d := by
        rw [norm_smul,norm_smul,hu,quarterTurn_norm,hu,
          Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (by positivity : 0<r/4),hs]
        ring
      _ < r := by linarith
  constructor
  · refine ⟨q+(-d) • quarterTurn u,⟨hball (-d) (by rw [abs_neg,abs_of_pos hd]),?_⟩,
      (Metric.ball_subset_ball hdε) hballs.2.1,hballs.2.2⟩
    change cross2 u (q+(-d) • quarterTurn u)<cross2 u p
    rw [← hqcross]
    exact hballs.2.2
  · refine ⟨q+d • quarterTurn u,⟨hball d (abs_of_pos hd),?_⟩,
      (Metric.ball_subset_ball hdε) hballs.1.1,hballs.1.2⟩
    change cross2 u p<cross2 u (q+d • quarterTurn u)
    rw [← hqcross]
    exact hballs.1.2

private theorem star_halfBall_clear {n : ℕ} (G : PennyGraph n) (v : Fin n)
    (r : ℝ) (hstar : ∀ z∈Metric.ball (G.point v) r,
      z∈G.drawing ↔ z=G.point v ∨ ∃ c : Fin n, G.graph.Adj v c ∧
        ∃ t : ℝ, 0<t ∧ t<r ∧ z=G.point v+t • (G.point c-G.point v))
    (u : Plane) :
    ((∀ c, G.graph.Adj v c → ¬ cross2 u (G.point c-G.point v)<0) →
      rightHalfBall u (G.point v) r ⊆ G.drawingᶜ) ∧
    ((∀ c, G.graph.Adj v c → ¬ 0<cross2 u (G.point c-G.point v)) →
      leftHalfBall u (G.point v) r ⊆ G.drawingᶜ) := by
  constructor
  · intro hn z hz hdraw
    rcases (hstar z hz.1).mp hdraw with rfl | ⟨c,hvc,t,ht,_,rfl⟩
    · exact (lt_irrefl _) (show cross2 u (G.point v)<cross2 u (G.point v) from hz.2)
    · apply hn c hvc
      have hc : cross2 u (G.point v+t • (G.point c-G.point v))<cross2 u (G.point v) := hz.2
      rw [cross2_add_right,cross2_smul_right] at hc
      by_contra hnonneg
      have hm := mul_nonneg ht.le (le_of_not_gt hnonneg)
      nlinarith
  · intro hn z hz hdraw
    rcases (hstar z hz.1).mp hdraw with rfl | ⟨c,hvc,t,ht,_,rfl⟩
    · exact (lt_irrefl _) (show cross2 u (G.point v)<cross2 u (G.point v) from hz.2)
    · apply hn c hvc
      have hc : cross2 u (G.point v)<cross2 u (G.point v+t • (G.point c-G.point v)) := hz.2
      rw [cross2_add_right,cross2_smul_right] at hc
      by_contra hnonpos
      have hm := mul_nonpos_of_nonneg_of_nonpos ht.le (le_of_not_gt hnonpos)
      nlinarith

theorem PennyGraph.empty_reflex_sector_face {n : ℕ} (G : PennyGraph n)
    (v a b : Fin n) (hva : G.graph.Adj v a) (hvb : G.graph.Adj v b)
    (hcross : 0<cross2 (G.point a-G.point v) (G.point b-G.point v))
    (hnoRight : ∀ c, G.graph.Adj v c → ¬ cross2 (G.point a-G.point v) (G.point c-G.point v)<0)
    (hnoLeft : ∀ c, G.graph.Adj v c → ¬ 0<cross2 (G.point b-G.point v) (G.point c-G.point v)) :
    G.sourceFace ⟨(v,a),hva⟩ = G.sourceFace (reverseEdge ⟨(v,b),hvb⟩) := by
  let p := G.point v
  let u := G.point a-G.point v
  let w := G.point b-G.point v
  let e : OrientedEdge G := ⟨(v,a),hva⟩
  let f : OrientedEdge G := ⟨(v,b),hvb⟩
  have hu : ‖u‖=1 := by simpa only [u,← dist_eq_norm] using hva.symm.2
  have hw : ‖w‖=1 := by simpa only [w,← dist_eq_norm] using hvb.symm.2
  obtain ⟨r,hr,hr1,hstar⟩ := G.vertex_local_star v
  have hA := (star_halfBall_clear G v r hstar u).1 hnoRight
  have hB := (star_halfBall_clear G v r hstar w).2 hnoLeft
  have hneg : cross2 (-w) (-u)<0 := by
    have hswap := fbo_cross_swap u w
    simpa [cross2] using (show cross2 w u<0 by linarith)
  have hmeet := clockwiseVertexSector_combination p (-w) (-u)
    (by simpa using hw) (by simpa using hu) hneg
    (show 0<r/4 by positivity) (show 0<r/4 by positivity) (show r/4+r/4<r by linarith)
  have hAB : (rightHalfBall u p r ∩ leftHalfBall w p r).Nonempty := by
    refine ⟨p+(r/4) • (-w)+(r/4) • (-u),?_,?_⟩
    · simpa only [leftHalfBall_neg] using hmeet.2
    · simpa only [rightHalfBall,leftHalfBall,cross2_neg_left,neg_lt_neg_iff] using hmeet.1
  have hpre := (isPreconnected_rightHalfBall u p r).union' hAB
    (isPreconnected_leftHalfBall w p r)
  have hsub : rightHalfBall u p r ∪ leftHalfBall w p r ⊆ G.drawingᶜ :=
    Set.union_subset hA hB
  have hs0 : 0<r/4 := by positivity
  have hs1 : r/4<1 := by linarith
  obtain ⟨ε,hε,hεsub⟩ := G.right_face_halfBall_at e hs0 hs1
  obtain ⟨δ,hδ,hδsub⟩ := G.left_face_halfBall_at f hs0 hs1
  obtain ⟨z,hz,hze⟩ := (unit_ray_halfBall_meets p u hu hr hε).1
  obtain ⟨y,hy,hyf⟩ := (unit_ray_halfBall_meets p w hw hr hδ).2
  have hepoint : G.edgePoint e.val.1 e.val.2 (r/4)=p+(r/4) • u := by
    dsimp [e,p,u,PennyGraph.edgePoint]
    module
  have hfpoint : G.edgePoint f.val.1 f.val.2 (r/4)=p+(r/4) • w := by
    dsimp [f,p,w,PennyGraph.edgePoint]
    module
  have hze' : z∈(G.sourceFace e).val := hεsub (by simpa only [hepoint,e,carriedVector,u] using hze)
  have hyf' : y∈(G.sourceFace (reverseEdge f)).val :=
    hδsub (by simpa only [hfpoint,f,carriedVector,w] using hyf)
  have hsame := hpre.subset_connectedComponentIn (Or.inl hz) hsub (Or.inr hy)
  apply Subtype.ext
  exact ((G.sourceFace e).property.eq_component hze').trans
    ((connectedComponentIn_eq hsame).trans ((G.sourceFace (reverseEdge f)).property.eq_component hyf').symm)

theorem PennyGraph.empty_antipodal_sector_face {n : ℕ} (G : PennyGraph n)
    (v a b : Fin n) (hva : G.graph.Adj v a) (hvb : G.graph.Adj v b)
    (hopposite : G.point b-G.point v = -(G.point a-G.point v))
    (hnoRight : ∀ c, G.graph.Adj v c → ¬ cross2 (G.point a-G.point v) (G.point c-G.point v)<0) :
    G.sourceFace ⟨(v,a),hva⟩ = G.sourceFace (reverseEdge ⟨(v,b),hvb⟩) := by
  let p := G.point v
  let u := G.point a-G.point v
  let w := G.point b-G.point v
  let e : OrientedEdge G := ⟨(v,a),hva⟩
  let f : OrientedEdge G := ⟨(v,b),hvb⟩
  have hu : ‖u‖=1 := by simpa only [u,← dist_eq_norm] using hva.symm.2
  have hw : ‖w‖=1 := by simpa only [w,← dist_eq_norm] using hvb.symm.2
  obtain ⟨r,hr,hr1,hstar⟩ := G.vertex_local_star v
  have hA := (star_halfBall_clear G v r hstar u).1 hnoRight
  have hs0 : 0<r/4 := by positivity
  have hs1 : r/4<1 := by linarith
  obtain ⟨ε,hε,hεsub⟩ := G.right_face_halfBall_at e hs0 hs1
  obtain ⟨δ,hδ,hδsub⟩ := G.left_face_halfBall_at f hs0 hs1
  obtain ⟨z,hz,hze⟩ := (unit_ray_halfBall_meets p u hu hr hε).1
  obtain ⟨y,hy,hyf⟩ := (unit_ray_halfBall_meets p w hw hr hδ).2
  have hyA : y∈rightHalfBall u p r := by
    simpa only [w,hopposite,leftHalfBall_neg] using hy
  have hepoint : G.edgePoint e.val.1 e.val.2 (r/4)=p+(r/4) • u := by
    dsimp [e,p,u,PennyGraph.edgePoint]
    module
  have hfpoint : G.edgePoint f.val.1 f.val.2 (r/4)=p+(r/4) • w := by
    dsimp [f,p,w,PennyGraph.edgePoint]
    module
  have hze' : z∈(G.sourceFace e).val := hεsub (by simpa only [hepoint,e,carriedVector,u] using hze)
  have hyf' : y∈(G.sourceFace (reverseEdge f)).val :=
    hδsub (by simpa only [hfpoint,f,carriedVector,w] using hyf)
  have hsame := (isPreconnected_rightHalfBall u p r).subset_connectedComponentIn hz hA hyA
  apply Subtype.ext
  exact ((G.sourceFace e).property.eq_component hze').trans
    ((connectedComponentIn_eq hsame).trans ((G.sourceFace (reverseEdge f)).property.eq_component hyf').symm)

theorem unit_cross_zero_eq_or_neg (u w : Plane) (hu : ‖u‖=1) (hw : ‖w‖=1)
    (hc : cross2 u w=0) : w=u ∨ w= -u := by
  have hdec : w=inner ℝ u w • u := by
    simpa only [hc,zero_smul,add_zero] using unit_direction_decomposition u w hu
  have hnorm := congrArg norm hdec
  rw [norm_smul,hu,hw,Real.norm_eq_abs,mul_one] at hnorm
  rcases le_total 0 (inner ℝ u w) with h | h
  · have hi : inner ℝ u w=1 := by rw [abs_of_nonneg h] at hnorm; linarith
    exact Or.inl (by rw [hdec,hi,one_smul])
  · have hi : inner ℝ u w= -1 := by rw [abs_of_nonpos h] at hnorm; linarith
    exact Or.inr (by rw [hdec,hi,neg_one_smul])

private theorem vertex_projective_gap {n : ℕ} (G : PennyGraph n) (v : Fin n)
    (u : Plane) (hu : ‖u‖=1)
    (hex : ∃ b : Fin n, G.graph.Adj v b ∧ cross2 u (G.point b-G.point v)<0) :
    ∃ b : Fin n, G.graph.Adj v b ∧ cross2 u (G.point b-G.point v)<0 ∧
      ∀ c : Fin n, G.graph.Adj v c →
        ¬ (cross2 u (G.point c-G.point v)<0 ∧
          0<cross2 (G.point b-G.point v) (G.point c-G.point v)) := by
  let direction (c : Fin n) := G.point c-G.point v
  let N : Finset (Fin n) := Finset.univ.filter
    (fun c => G.graph.Adj v c ∧ cross2 u (direction c)<0)
  have hN : N.Nonempty := by
    obtain ⟨b,hb,hcross⟩ := hex
    exact ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb,hcross⟩⟩
  let slope (c : Fin n) := inner ℝ u (direction c)/(-cross2 u (direction c))
  obtain ⟨b,hb,hmax⟩ := N.exists_max_image slope hN
  have hb' := (Finset.mem_filter.mp hb).2
  refine ⟨b,hb'.1,hb'.2,?_⟩
  intro c hvc hc
  have hcN : c∈N := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvc,hc.1⟩
  have hbound := hmax c hcN
  have hid := cross2_in_unit_frame u (direction b) (direction c) hu
  have hlt : slope b<slope c := by
    apply (div_lt_div_iff₀ (neg_pos.mpr hb'.2) (neg_pos.mpr hc.1)).mpr
    nlinarith [hc.2]
  exact (not_lt_of_ge hbound) hlt

theorem PennyGraph.degree_one_incident_faces_eq {n : ℕ} (G : PennyGraph n)
    (v a : Fin n) (hva : G.graph.Adj v a)
    (hdegree : ∀ b, G.graph.Adj v b → b=a) :
    G.sourceFace ⟨(v,a),hva⟩ = G.sourceFace (reverseEdge ⟨(v,a),hva⟩) := by
  let e : OrientedEdge G := ⟨(v,a),hva⟩
  let f := physicalEdge e
  let S := (Finset.univ : Finset (ContactEdge G)).erase f
  have hf : f∉S := Finset.notMem_erase _ _
  have hpair : s(f.val.1,f.val.2)=s(v,a) := by
    by_cases h : v<a
    · simp [f,e,physicalEdge,h]
    · simpa only [f,e,physicalEdge,dite_eq_right h] using (Sym2.eq_swap (a := a) (b := v))
  have hv : ∀ g∈S, g.val.1≠v ∧ g.val.2≠v := by
    intro g hg
    have hgf : g≠f := (Finset.mem_erase.mp hg).1
    constructor
    · intro hgv
      have hga : g.val.2=a := hdegree _ (by simpa only [← hgv] using g.property.2)
      apply hgf
      apply g.eq_of_unordered_eq f
      rw [hgv,hga,hpair]
    · intro hgv
      have hga : g.val.1=a := hdegree _ (by simpa only [← hgv] using g.property.2.symm)
      apply hgf
      apply g.eq_of_unordered_eq f
      rw [hgv,hga,hpair]
      exact Sym2.eq_swap
  have hsides : connectedComponentIn (G.subdrawing (insert f S))ᶜ
      (G.edgeSidePoint S f true (1/2)) =
      connectedComponentIn (G.subdrawing (insert f S))ᶜ (G.edgeSidePoint S f false (1/2)) := by
    by_cases h : v<a
    · have hfval : f.val=(v,a) := by simp [f,e,physicalEdge,h]
      exact G.insert_edge_sides_eq_of_isolated_left S f hf (by simpa only [hfval] using hv)
    · have hfval : f.val=(a,v) := by simp [f,e,physicalEdge,h]
      exact G.insert_edge_sides_eq_of_isolated_right S f hf (by simpa only [hfval] using hv)
  have hdrawing : G.subdrawing (insert f S)=G.drawing := by
    simp only [S,Finset.insert_erase (Finset.mem_univ _),G.subdrawing_univ]
  rw [hdrawing,G.contact_left_component_eq_sourceFace f,G.contact_right_component_eq_sourceFace f] at hsides
  have hfaces : G.sourceFace (reverseEdge f.forwardEdge)=G.sourceFace f.forwardEdge := Subtype.ext hsides
  by_cases h : v<a
  · have heq : f.forwardEdge=e := by apply Subtype.ext; simp [f,e,physicalEdge,h,ContactEdge.forwardEdge]
    rw [heq] at hfaces
    exact hfaces.symm
  · have heq : reverseEdge f.forwardEdge=e := by
      apply Subtype.ext
      simp [f,e,physicalEdge,h,ContactEdge.forwardEdge,reverseEdge]
    have hrev : f.forwardEdge=reverseEdge e := by
      simpa only [reverseEdge_involutive] using congrArg reverseEdge heq
    rw [heq,hrev] at hfaces
    exact hfaces

theorem PennyGraph.vertex_face_continuation {n : ℕ} (G : PennyGraph n)
    (v a : Fin n) (hva : G.graph.Adj v a) :
    ∃ b : Fin n, ∃ hvb : G.graph.Adj v b,
      G.sourceFace ⟨(v,a),hva⟩ = G.sourceFace (reverseEdge ⟨(v,b),hvb⟩) ∧
      (b=a → ∀ c, G.graph.Adj v c → c=a) := by
  let u := G.point a-G.point v
  have hu : ‖u‖=1 := by simpa only [u,← dist_eq_norm] using hva.symm.2
  by_cases hright : ∃ b : Fin n, G.graph.Adj v b ∧ cross2 u (G.point b-G.point v)<0
  · obtain ⟨b,hvb,hcross,_,hface⟩ := G.clockwise_successor_in_right_halfPlane v a hva hright
    refine ⟨b,hvb,hface,?_⟩
    intro heq
    subst b
    have hc : cross2 u u<0 := hcross
    rw [cross2_self] at hc
    exact False.elim (lt_irrefl _ hc)
  have hnoRight (c) (hc : G.graph.Adj v c) : ¬ cross2 u (G.point c-G.point v)<0 :=
    fun h => hright ⟨c,hc,h⟩
  by_cases hantipode : ∃ b : Fin n, G.graph.Adj v b ∧ G.point b-G.point v = -u
  · obtain ⟨b,hvb,hopp⟩ := hantipode
    refine ⟨b,hvb,G.empty_antipodal_sector_face v a b hva hvb hopp hnoRight,?_⟩
    intro heq
    subst b
    have hopp' : u= -u := hopp
    have h2 : (2 : ℝ) • u=0 := by
      rw [two_smul]
      calc
        u+u=u+(-u) := congrArg (fun z : Plane => u+z) hopp'
        _=0 := add_neg_cancel u
    have hz : u=0 := (smul_eq_zero.mp h2).resolve_left (by norm_num)
    rw [hz,norm_zero] at hu
    exact False.elim (by norm_num at hu)
  by_cases hleft : ∃ b : Fin n, G.graph.Adj v b ∧ 0<cross2 u (G.point b-G.point v)
  · have hex : ∃ b : Fin n, G.graph.Adj v b ∧ cross2 (-u) (G.point b-G.point v)<0 := by
      obtain ⟨b,hb,hbpos⟩ := hleft
      refine ⟨b,hb,?_⟩
      rw [cross2_neg_left]
      linarith
    obtain ⟨b,hvb,hb,hgap⟩ := vertex_projective_gap G v (-u) (by simpa using hu) hex
    have hbpos : 0<cross2 u (G.point b-G.point v) := by
      rw [cross2_neg_left] at hb
      linarith
    have hnoLeft (c) (hvc : G.graph.Adj v c) :
        ¬ 0<cross2 (G.point b-G.point v) (G.point c-G.point v) := by
      intro hbc
      have huc : 0≤cross2 u (G.point c-G.point v) := le_of_not_gt (hnoRight c hvc)
      rcases eq_or_lt_of_le huc with hzero | hpos
      · have hcunit : ‖G.point c-G.point v‖=1 := by
          simpa only [← dist_eq_norm] using hvc.symm.2
        rcases unit_cross_zero_eq_or_neg u (G.point c-G.point v) hu hcunit hzero.symm with hsame | hopp
        · rw [hsame,fbo_cross_swap u (G.point b-G.point v)] at hbc
          linarith
        · exact hantipode ⟨c,hvc,hopp⟩
      · apply hgap c hvc
        exact ⟨by rw [cross2_neg_left]; linarith,hbc⟩
    refine ⟨b,hvb,G.empty_reflex_sector_face v a b hva hvb hbpos hnoRight hnoLeft,?_⟩
    intro heq
    subst b
    have hc : 0<cross2 u u := hbpos
    rw [cross2_self] at hc
    exact False.elim (lt_irrefl _ hc)
  · have hdegree (c) (hvc : G.graph.Adj v c) : c=a := by
      have hzero : cross2 u (G.point c-G.point v)=0 :=
        le_antisymm (le_of_not_gt (fun h => hleft ⟨c,hvc,h⟩)) (le_of_not_gt (hnoRight c hvc))
      have hcunit : ‖G.point c-G.point v‖=1 := by simpa only [← dist_eq_norm] using hvc.symm.2
      rcases unit_cross_zero_eq_or_neg u (G.point c-G.point v) hu hcunit hzero with hsame | hopp
      · apply G.point_injective
        have heq : G.point c-G.point v = G.point a-G.point v := hsame
        simpa only [sub_add_cancel] using congrArg (fun z : Plane => z+G.point v) heq
      · exact False.elim (hantipode ⟨c,hvc,hopp⟩)
    exact ⟨a,hva,G.degree_one_incident_faces_eq v a hva hdegree,fun _ => hdegree⟩

end Swanepoel
