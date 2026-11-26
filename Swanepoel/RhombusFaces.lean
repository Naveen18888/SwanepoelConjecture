module
public import Swanepoel.RhombusBoundary
@[expose] public section

noncomputable section
namespace Swanepoel

theorem PennyGraph.edgeTrace_reverse {n : ℕ} (G : PennyGraph n) (a b : Fin n) :
    G.edgeTrace a b=G.edgeTrace b a := by
  have h (a b : Fin n) : G.edgeTrace a b⊆G.edgeTrace b a := by
    rintro z ⟨t,⟨ht0,ht1⟩,rfl⟩
    exact ⟨1-t,⟨by linarith,by linarith⟩,G.edgePoint_reverse a b t⟩
  exact Set.Subset.antisymm (h a b) (h b a)

theorem PennyGraph.edgeTrace_eq_of_unordered_eq {n : ℕ} (G : PennyGraph n)
    (a b c d : Fin n) (h : s(a,b)=s(c,d)) : G.edgeTrace a b=G.edgeTrace c d := by
  rcases Sym2.eq_iff.mp h with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · rw [h1,h2]
  · rw [h1,h2]
    exact G.edgeTrace_reverse d c

namespace RhombusCell
variable {n : ℕ} {G : PennyGraph n} (C : RhombusCell G)

def IsSide (a b : Fin n) : Prop := s(a,b)=s(C.a,C.b) ∨ s(a,b)=s(C.b,C.c) ∨
  s(a,b)=s(C.c,C.d) ∨ s(a,b)=s(C.d,C.a)

theorem edgeTrace_subset_boundary_of_isSide (a b : Fin n) (hs : C.IsSide a b) :
    G.edgeTrace a b⊆C.boundary := by
  intro z hz
  rcases hs with hs | hs | hs | hs
  · rw [G.edgeTrace_eq_of_unordered_eq _ _ _ _ hs] at hz
    exact Or.inl (Or.inl (Or.inl hz))
  · rw [G.edgeTrace_eq_of_unordered_eq _ _ _ _ hs] at hz
    exact Or.inl (Or.inl (Or.inr hz))
  · rw [G.edgeTrace_eq_of_unordered_eq _ _ _ _ hs] at hz
    exact Or.inl (Or.inr hz)
  · rw [G.edgeTrace_eq_of_unordered_eq _ _ _ _ hs] at hz
    exact Or.inr hz

theorem openEdgeTrace_disjoint_boundary (a b : Fin n) (hab : G.graph.Adj a b)
    (hs : ¬ C.IsSide a b) : _root_.Disjoint (G.openEdgeTrace a b) C.boundary := by
  apply Set.disjoint_left.mpr
  rintro z ⟨t,⟨ht0,ht1⟩,rfl⟩ hz
  rcases hz with ((hz | hz) | hz) | hz
  all_goals obtain ⟨s,⟨hs0,hs1⟩,he⟩ := hz
  · exact hs (Or.inl (G.interior_edge_intersection _ _ _ _ hab C.ab ht0 ht1 hs0 hs1 he.symm))
  · exact hs (Or.inr (Or.inl (G.interior_edge_intersection _ _ _ _ hab C.bc ht0 ht1 hs0 hs1 he.symm)))
  · exact hs (Or.inr (Or.inr (Or.inl
      (G.interior_edge_intersection _ _ _ _ hab C.cd ht0 ht1 hs0 hs1 he.symm))))
  · exact hs (Or.inr (Or.inr (Or.inr
      (G.interior_edge_intersection _ _ _ _ hab C.da ht0 ht1 hs0 hs1 he.symm))))

theorem edgeTrace_disjoint_openRegion (ht : G.TriangleFree) (a b : Fin n)
    (hab : G.graph.Adj a b) : _root_.Disjoint (G.edgeTrace a b) C.openRegion := by
  classical
  by_cases hs : C.IsSide a b
  · exact (C.boundary_disjoint_openRegion ht).mono_left (C.edgeTrace_subset_boundary_of_isSide a b hs)
  apply Set.disjoint_left.mpr
  rintro z ⟨t,⟨ht0,ht1⟩,rfl⟩ hz
  by_cases h0 : t=0
  · subst t
    simp only [PennyGraph.edgePoint,sub_zero,one_smul,zero_smul,add_zero] at hz
    exact C.vertex_not_mem_openRegion ht a hz
  by_cases h1 : t=1
  · subst t
    simp only [PennyGraph.edgePoint,sub_self,zero_smul,one_smul,zero_add] at hz
    exact C.vertex_not_mem_openRegion ht b hz
  have ht0' : 0<t := lt_of_le_of_ne ht0 (Ne.symm h0)
  have ht1' : t<1 := lt_of_le_of_ne ht1 h1
  have hboundary := C.openEdgeTrace_disjoint_boundary a b hab hs
  have hall : G.openEdgeTrace a b⊆C.openRegion := by
    apply (G.isPreconnected_openEdgeTrace a b).subset_of_closure_inter_subset C.isOpen_openRegion
      ⟨G.edgePoint a b t,⟨t,⟨ht0',ht1'⟩,rfl⟩,hz⟩
    rintro w ⟨hw,hwe⟩
    rcases C.closedRegion_subset_open_union_boundary ht (C.closure_openRegion_subset hw) with ho | hb
    · exact ho
    · exact False.elim (Set.disjoint_left.mp hboundary hwe hb)
  have htrace : G.edgeTrace a b⊆C.closedRegion :=
    (G.edgeTrace_subset_closure_openEdgeTrace a b).trans
      (closure_minimal (hall.trans C.openRegion_subset_closedRegion) C.isClosed_closedRegion)
  have ha : G.point a∈C.closedRegion := htrace
    ⟨0,⟨by norm_num,by norm_num⟩,by simp [PennyGraph.edgePoint]⟩
  have hb : G.point b∈C.closedRegion := htrace
    ⟨1,⟨by norm_num,by norm_num⟩,by simp [PennyGraph.edgePoint]⟩
  exact hs (C.adj_inside ht a b (C.vertex_mem_corners_of_mem_closedRegion ht a ha)
    (C.vertex_mem_corners_of_mem_closedRegion ht b hb) hab)

theorem openRegion_subset_complement (ht : G.TriangleFree) : C.openRegion⊆G.drawingᶜ := by
  intro z hz hdraw
  rcases hdraw with ⟨i,rfl⟩ | he
  · exact C.vertex_not_mem_openRegion ht i hz
  · obtain ⟨e,he⟩ := Set.mem_iUnion.mp he
    exact Set.disjoint_left.mp (C.edgeTrace_disjoint_openRegion ht _ _ e.property) he hz

theorem openRegion_eq_connectedComponentIn (ht : G.TriangleFree) :
    C.openRegion=connectedComponentIn G.drawingᶜ (C.cellPoint (1/2) (1/2)) := by
  have hz : C.cellPoint (1/2) (1/2)∈C.openRegion :=
    C.cellPoint_mem_openRegion ht (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  apply Set.Subset.antisymm
  · exact (C.isPreconnected_openRegion ht).subset_connectedComponentIn hz (C.openRegion_subset_complement ht)
  · apply isPreconnected_connectedComponentIn.subset_of_closure_inter_subset C.isOpen_openRegion
      ⟨C.cellPoint (1/2) (1/2),mem_connectedComponentIn (C.openRegion_subset_complement ht hz),hz⟩
    rintro z ⟨hcl,hcomp⟩
    rcases C.closedRegion_subset_open_union_boundary ht (C.closure_openRegion_subset hcl) with ho | hb
    · exact ho
    · exact False.elim ((connectedComponentIn_subset G.drawingᶜ _ hcomp) (C.boundary_subset_drawing hb))

theorem isBounded_openRegion (ht : G.TriangleFree) : Bornology.IsBounded C.openRegion := by
  apply Metric.isBounded_closedBall (x := G.point C.a) (r := 2) |>.subset
  intro z hz
  have hu : ‖C.u‖=1 := by simpa only [u,← dist_eq_norm] using C.ab.symm.2
  have hv : ‖C.v‖=1 := by simpa only [v,← dist_eq_norm] using C.da.2
  obtain ⟨hr0,hr1,hs0,hs1⟩ := hz
  have he : z-G.point C.a=C.coordU z • C.u+C.coordV z • C.v := by
    have hh := C.reconstruct ht z
    dsimp [cellPoint] at hh
    calc
      _ = (G.point C.a+C.coordU z • C.u+C.coordV z • C.v)-G.point C.a :=
        congrArg (fun x : Plane => x-G.point C.a) hh.symm
      _ = _ := by abel
  have hn := norm_add_le (C.coordU z • C.u) (C.coordV z • C.v)
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hr0,abs_of_pos hs0,hu,hv] at hn
  rw [Metric.mem_closedBall,dist_eq_norm,he]
  linarith

end RhombusCell

def PennyGraph.IsFace {n : ℕ} (G : PennyGraph n) (F : Set Plane) : Prop :=
  ∃ z ∈ G.drawingᶜ, F=connectedComponentIn G.drawingᶜ z

abbrev BoundedFace {n : ℕ} (G : PennyGraph n) :=
  {F : Set Plane // G.IsFace F ∧ Bornology.IsBounded F}

theorem RhombusCell.isBoundedFace {n : ℕ} {G : PennyGraph n} (C : RhombusCell G)
    (ht : G.TriangleFree) : G.IsFace C.openRegion ∧ Bornology.IsBounded C.openRegion := by
  refine ⟨⟨C.cellPoint (1/2) (1/2),?_,C.openRegion_eq_connectedComponentIn ht⟩,C.isBounded_openRegion ht⟩
  exact C.openRegion_subset_complement ht
    (C.cellPoint_mem_openRegion ht (by norm_num) (by norm_num) (by norm_num) (by norm_num))

end Swanepoel
