module
public import Swanepoel.FaceBoundaryOrder
public import Swanepoel.RayGeneric
public import Swanepoel.TrackClassification
@[expose] public section

noncomputable section
namespace Swanepoel
open Set Metric
attribute [local instance] Classical.propDecidable

theorem bounded_open_first_ray_exit (F : Set Plane) (hopen : IsOpen F)
    (hb : Bornology.IsBounded F) (z d : Plane) (hz : z∈F) (hd : d≠0) :
    ∃ t : ℝ, 0<t ∧ z-t • d ∈ frontier F ∧
      ∀ s : ℝ, 0≤s → s<t → z-s • d ∈ F := by
  let ray (t : ℝ) := z-t • d
  have hcont : Continuous ray := continuous_const.sub (continuous_id.smul continuous_const)
  let T : Set ℝ := {t | 0≤t ∧ ray t∉F}
  have hTclosed : IsClosed T :=
    isClosed_Ici.inter (hopen.isClosed_compl.preimage hcont)
  have hdn : 0<‖d‖ := norm_pos_iff.mpr hd
  obtain ⟨R,hR⟩ := isBounded_iff_forall_norm_le.mp hb
  have hR0 : 0≤R := (norm_nonneg z).trans (hR z hz)
  let t0 := (R+‖z‖+1)/‖d‖
  have ht0 : 0<t0 := div_pos (by positivity) hdn
  have ht0mul : t0*‖d‖=R+‖z‖+1 := div_mul_cancel₀ _ hdn.ne'
  have hlower : t0*‖d‖-‖z‖≤‖ray t0‖ := by
    have h := norm_sub_norm_le (t0 • d) z
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht0] at h
    rw [norm_sub_rev] at h
    exact h
  have ht0out : ray t0∉F := by
    intro h
    have hbound := hR (ray t0) h
    nlinarith
  have hTne : T.Nonempty := ⟨t0,ht0.le,ht0out⟩
  have hTbelow : BddBelow T := ⟨0,fun _ ht => ht.1⟩
  let t := sInf T
  have hleast : IsLeast T t := hTclosed.isLeast_csInf hTne hTbelow
  have htpos : 0<t := by
    by_contra hn
    have heq : t=0 := le_antisymm (le_of_not_gt hn) hleast.1.1
    apply hleast.1.2
    simpa only [ray,heq,zero_smul,sub_zero] using hz
  have hin (s : ℝ) (hs0 : 0≤s) (hst : s<t) : ray s∈F := by
    by_contra hn
    exact (not_lt_of_ge (hleast.2 ⟨hs0,hn⟩)) hst
  have htcl : t∈closure (Ico (0 : ℝ) t) := by
    rw [closure_Ico (show (0 : ℝ)≠t by linarith)]
    exact ⟨htpos.le,le_rfl⟩
  have hsub : ray '' Ico (0 : ℝ) t ⊆ F := by
    rintro _ ⟨s,hs,rfl⟩
    exact hin s hs.1 hs.2
  have hpcl : ray t∈closure F := closure_mono hsub
    (image_closure_subset_closure_image hcont ⟨t,htcl,rfl⟩)
  refine ⟨t,htpos,?_,hin⟩
  rw [frontier,hopen.interior_eq]
  exact ⟨hpcl,hleast.1.2⟩

private theorem approach_first_exit (F : Set Plane) (z d : Plane) (hd : d≠0)
    {t ε : ℝ} (ht : 0<t) (hε : 0<ε)
    (hin : ∀ s : ℝ, 0≤s → s<t → z-s • d∈F) :
    ∃ δ : ℝ, 0<δ ∧ (z-t • d)+δ • d∈F ∧
      (z-t • d)+δ • d∈Metric.ball (z-t • d) ε := by
  let δ := min (t/2) (ε/(2*‖d‖))
  have hdn : 0<‖d‖ := norm_pos_iff.mpr hd
  have hδ : 0<δ := lt_min (by positivity) (div_pos hε (by positivity))
  have hδt : δ≤t/2 := min_le_left _ _
  have hδε : δ*(2*‖d‖)≤ε :=
    (le_div_iff₀ (by positivity : 0<2*‖d‖)).mp (min_le_right (t/2) (ε/(2*‖d‖)))
  have hrepr : (z-t • d)+δ • d=z-(t-δ) • d := by module
  refine ⟨δ,hδ,?_,?_⟩
  · rw [hrepr]
    exact hin (t-δ) (by linarith) (by linarith)
  · rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,
      Real.norm_eq_abs,abs_of_pos hδ]
    nlinarith

theorem sourceNormal_inner_eq_cross {n : ℕ} {G : PennyGraph n} (e : OrientedEdge G) (d : Plane) :
    inner ℝ d (sourceNormal e)=cross2 d (carriedVector e) := by
  simp [sourceNormal,quarterTurn,cross2,PiLp.inner_apply,Fin.sum_univ_two]
  ring

private theorem fds_cross_swap (u v : Plane) : cross2 u v= -cross2 v u := by
  unfold cross2
  ring

theorem PennyGraph.bounded_face_positive_ray_exit {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) (hb : Bornology.IsBounded F.val) (z d : Plane)
    (hz : z∈F.val) (hd : d≠0)
    (hgeneric : ∀ i : Fin n, cross2 d z≠cross2 d (G.point i)) :
    ∃ t : ℝ, 0<t ∧ ∃ e : OrientedEdge G, ∃ s∈Ioo (0 : ℝ) 1,
      z-t • d=G.edgePoint e.val.1 e.val.2 s ∧ G.sourceFace e=F ∧
        0 < inner ℝ d (sourceNormal e) := by
  obtain ⟨t,ht,hfront,hin⟩ := bounded_open_first_ray_exit F.val F.property.isOpen hb z d hz hd
  let p := z-t • d
  have hpCross : cross2 d p=cross2 d z := by
    dsimp [p]
    rw [cross2_sub_right,cross2_smul_right,cross2_self,mul_zero,sub_zero]
  have hpNe (i : Fin n) : p≠G.point i := by
    intro h
    exact hgeneric i (hpCross.symm.trans (congrArg (cross2 d) h))
  have hpDraw : p∈G.drawing := G.face_frontier_subset_drawing F hfront
  have hcontact : ∃ e : OrientedEdge G, ∃ s∈Ioo (0 : ℝ) 1,
      p=G.edgePoint e.val.1 e.val.2 s ∧ cross2 (carriedVector e) d<0 := by
    rcases hpDraw with ⟨i,hi⟩ | hedge
    · exact False.elim (hpNe i hi.symm)
    obtain ⟨e,he⟩ := Set.mem_iUnion.mp hedge
    obtain ⟨s,hs,hpoint⟩ := he
    have hs0 : 0<s := by
      by_contra hn
      have hsz : s=0 := le_antisymm (le_of_not_gt hn) hs.1
      apply hpNe e.val.1
      simpa [hsz,PennyGraph.edgePoint] using hpoint.symm
    have hs1 : s<1 := by
      by_contra hn
      have hsz : s=1 := le_antisymm hs.2 (le_of_not_gt hn)
      apply hpNe e.val.2
      simpa [hsz,PennyGraph.edgePoint] using hpoint.symm
    have hcrossNe : cross2 (carriedVector e) d≠0 := by
      intro hzero
      have hreverse : cross2 d (carriedVector e)=0 := by rw [fds_cross_swap,hzero,neg_zero]
      have hrepr : G.edgePoint e.val.1 e.val.2 s=G.point e.val.1+s • carriedVector e := by
        dsimp [PennyGraph.edgePoint,carriedVector]
        module
      have hpEdge : cross2 d p=cross2 d (G.point e.val.1) := by
        rw [← hpoint,hrepr,cross2_add_right,cross2_smul_right,hreverse,mul_zero,add_zero]
      exact hgeneric e.val.1 (hpCross.symm.trans hpEdge)
    rcases lt_or_gt_of_ne hcrossNe with hneg | hpos
    · exact ⟨e,s,⟨hs0,hs1⟩,hpoint.symm,hneg⟩
    · refine ⟨reverseEdge e,1-s,⟨by linarith,by linarith⟩,?_,?_⟩
      · exact hpoint.symm.trans (G.edgePoint_reverse e.val.1 e.val.2 s).symm
      · rw [reverseEdge_vector,cross2_neg_left]
        linarith
  obtain ⟨e,s,hs,hpoint,hcross⟩ := hcontact
  obtain ⟨ε,hε,hhalf⟩ := G.right_face_halfBall_at e hs.1 hs.2
  obtain ⟨δ,hδ,hyF,hyBall⟩ := approach_first_exit F.val z d hd ht hε hin
  have hyRight : p+δ • d∈rightHalfBall (carriedVector e) p ε := by
    refine ⟨hyBall,?_⟩
    change cross2 (carriedVector e) (p+δ • d)<cross2 (carriedVector e) p
    rw [cross2_add_right,cross2_smul_right]
    exact add_lt_of_neg_right _ (mul_neg_of_pos_of_neg hδ hcross)
  have hyFace : p+δ • d∈(G.sourceFace e).val := by
    apply hhalf
    rwa [← hpoint]
  have heFace : G.sourceFace e=F := by
    apply Subtype.ext
    exact ((G.sourceFace e).property.eq_component hyFace).trans (F.property.eq_component hyF).symm
  have hnormal : 0 < inner ℝ d (sourceNormal e) := by
    rw [sourceNormal_inner_eq_cross,fds_cross_swap]
    exact neg_pos.mpr hcross
  exact ⟨t,ht,e,s,hs,hpoint,heFace,hnormal⟩

private theorem center_mem_closure_rightHalfBall (u p : Plane) (hu : ‖u‖=1)
    {r : ℝ} (hr : 0<r) : p∈closure (rightHalfBall u p r) := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let d := min (r/4) (ε/4)
  have hd : 0<d := lt_min (by positivity) (by positivity)
  have hdr : 2*d≤r := by have := min_le_left (r/4) (ε/4); dsimp [d]; linarith
  have hdε : 2*d≤ε := by have := min_le_right (r/4) (ε/4); dsimp [d]; linarith
  have hmem := (normal_offset_mem_halfBalls u p hu hd).2
  refine ⟨p+(-d) • quarterTurn u,⟨(Metric.ball_subset_ball hdr) hmem.1,hmem.2⟩,?_⟩
  have hdist : dist p (p+(-d) • quarterTurn u)<2*d := by
    simpa only [dist_comm] using Metric.mem_ball.mp hmem.1
  exact hdist.trans_le hdε

theorem PennyGraph.edgePoint_mem_closure_sourceFace {n : ℕ} (G : PennyGraph n)
    (e : OrientedEdge G) {t : ℝ} (ht0 : 0<t) (ht1 : t<1) :
    G.edgePoint e.val.1 e.val.2 t∈closure (G.sourceFace e).val := by
  obtain ⟨r,hr,hsub⟩ := G.right_face_halfBall_at e ht0 ht1
  exact closure_mono hsub (center_mem_closure_rightHalfBall _ _ (carriedVector_norm e) hr)

theorem PennyGraph.edgeTrace_subset_closure_sourceFace {n : ℕ} (G : PennyGraph n)
    (e : OrientedEdge G) : G.edgeTrace e.val.1 e.val.2⊆closure (G.sourceFace e).val := by
  have hopen : G.openEdgeTrace e.val.1 e.val.2⊆closure (G.sourceFace e).val := by
    rintro _ ⟨t,ht,rfl⟩
    exact G.edgePoint_mem_closure_sourceFace e ht.1 ht.2
  exact (G.edgeTrace_subset_closure_openEdgeTrace _ _).trans (closure_minimal hopen isClosed_closure)

theorem PennyGraph.sourceFace_endpoints_mem_closure {n : ℕ} (G : PennyGraph n)
    (e : OrientedEdge G) : G.point e.val.1∈closure (G.sourceFace e).val ∧
      G.point e.val.2∈closure (G.sourceFace e).val := by
  constructor
  · apply G.edgeTrace_subset_closure_sourceFace e
    exact ⟨0,⟨by norm_num,by norm_num⟩,by simp [PennyGraph.edgePoint]⟩
  · apply G.edgeTrace_subset_closure_sourceFace e
    exact ⟨1,⟨by norm_num,by norm_num⟩,by simp [PennyGraph.edgePoint]⟩

theorem PennyGraph.defect_meets_semicircle {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (hF : F∈G.defectPlaneFaces ht)
    (d : Plane) (hd : d≠0) :
    ∃ e∈G.faceSourcePorts F, 0 < inner ℝ d (sourceNormal e) := by
  obtain ⟨z,hz,hgeneric,_⟩ := G.exists_vertex_avoiding_parallel_line d hd F.val
    F.property.isOpen F.property.nonempty
  obtain ⟨_,_,e,_,_,_,he,hpositive⟩ := G.bounded_face_positive_ray_exit F
    (G.defectPlaneFace_isBounded ht hF) z d hz hd hgeneric
  refine ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,he⟩,hpositive⟩
  apply G.spineSource_of_sourceFace_mem_defects ht
  rw [he]
  exact hF

theorem PennyGraph.unique_positive_incident_right_support {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) (hb : Bornology.IsBounded F.val) (d : Plane) (hd : d≠0)
    (cap : OrientedEdge G)
    (hunique : ∀ e : OrientedEdge G, G.sourceFace e=F →
      0 < inner ℝ d (sourceNormal e) → e=cap) :
    ∀ z∈closure F.val, cross2 (carriedVector cap) (z-G.point cap.val.1)≤0 := by
  let u := carriedVector cap
  let A := G.point cap.val.1
  let H : Set Plane := {z | cross2 u (z-A)≤0}
  have hcont : Continuous (fun z : Plane => cross2 u (z-A)) :=
    (crossLinear u).continuous_of_finiteDimensional.comp (continuous_id.sub continuous_const)
  have hH : IsClosed H := isClosed_le hcont continuous_const
  have hsub : F.val⊆H := by
    intro z hz
    by_contra hbad
    have hbad' : 0<cross2 u (z-A) := lt_of_not_ge hbad
    let U : Set Plane := F.val ∩ {q | 0<cross2 u (q-A)}
    have hU : IsOpen U := F.property.isOpen.inter (isOpen_lt continuous_const hcont)
    have hUne : U.Nonempty := ⟨z,hz,hbad'⟩
    obtain ⟨q,hq,hgeneric,_⟩ := G.exists_vertex_avoiding_parallel_line d hd U hU hUne
    obtain ⟨t,ht,e,s,hs,hpoint,hface,hpositive⟩ :=
      G.bounded_face_positive_ray_exit F hb q d hq.1 hd hgeneric
    have heq : e=cap := hunique e hface hpositive
    subst e
    have hline : cross2 u ((q-t • d)-A)=0 := by
      rw [hpoint]
      have hrepr : G.edgePoint cap.val.1 cap.val.2 s-A=s • u := by
        dsimp [PennyGraph.edgePoint,A,u,carriedVector]
        module
      rw [hrepr,cross2_smul_right,cross2_self,mul_zero]
    have hsplit : (q-t • d)-A=(q-A)-t • d := by abel
    rw [hsplit,cross2_sub_right,cross2_smul_right] at hline
    have hcross : cross2 u d<0 := by
      rw [sourceNormal_inner_eq_cross,fds_cross_swap] at hpositive
      change 0< -cross2 u d at hpositive
      exact neg_pos.mp hpositive
    have hneg := mul_neg_of_pos_of_neg ht hcross
    have hqpos : 0<cross2 u (q-A) := hq.2
    nlinarith
  exact closure_minimal hsub hH

theorem PennyGraph.unique_positive_defect_port_right_support {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (hF : F∈G.defectPlaneFaces ht)
    (d : Plane) (hd : d≠0) (cap : OrientedEdge G)
    (hunique : ∀ e∈G.faceSourcePorts F, 0 < inner ℝ d (sourceNormal e) → e=cap) :
    ∀ z∈closure F.val, cross2 (carriedVector cap) (z-G.point cap.val.1)≤0 := by
  apply G.unique_positive_incident_right_support F (G.defectPlaneFace_isBounded ht hF) d hd cap
  intro e he hpos
  apply hunique e ?_ hpos
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_,he⟩
  apply G.spineSource_of_sourceFace_mem_defects ht
  rw [he]
  exact hF

end Swanepoel
