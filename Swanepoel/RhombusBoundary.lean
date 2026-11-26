module
public import Swanepoel.RhombusRegions
@[expose] public section

noncomputable section
namespace Swanepoel
namespace RhombusCell
variable {n : ℕ} {G : PennyGraph n} (C : RhombusCell G)

theorem edgePoint_ab (t : ℝ) : G.edgePoint C.a C.b t=C.cellPoint t 0 := by
  dsimp [PennyGraph.edgePoint,cellPoint,u,v]
  module

theorem edgePoint_bc (t : ℝ) : G.edgePoint C.b C.c t=C.cellPoint 1 t := by
  have hc : G.point C.c=G.point C.b+G.point C.d-G.point C.a :=
    (eq_sub_iff_add_eq).mpr (by simpa [add_comm] using C.parallelogram)
  dsimp [PennyGraph.edgePoint,cellPoint,u,v]
  rw [hc]
  module

theorem edgePoint_cd (t : ℝ) : G.edgePoint C.c C.d t=C.cellPoint (1-t) 1 := by
  have hc : G.point C.c=G.point C.b+G.point C.d-G.point C.a :=
    (eq_sub_iff_add_eq).mpr (by simpa [add_comm] using C.parallelogram)
  dsimp [PennyGraph.edgePoint,cellPoint,u,v]
  rw [hc]
  module

theorem edgePoint_da (t : ℝ) : G.edgePoint C.d C.a t=C.cellPoint 0 (1-t) := by
  dsimp [PennyGraph.edgePoint,cellPoint,u,v]
  module

theorem cellPoint_mem_boundary {r s : ℝ} (hr0 : 0≤r) (hr1 : r≤1) (hs0 : 0≤s) (hs1 : s≤1)
    (hb : r=0 ∨ r=1 ∨ s=0 ∨ s=1) : C.cellPoint r s∈C.boundary := by
  rcases hb with rfl | rfl | rfl | rfl
  · exact Or.inr ⟨1-s,⟨by linarith,by linarith⟩,by
      rw [C.edgePoint_da,show 1-(1-s)=s by ring]⟩
  · exact Or.inl (Or.inl (Or.inr ⟨s,⟨hs0,hs1⟩,C.edgePoint_bc s⟩))
  · exact Or.inl (Or.inl (Or.inl ⟨r,⟨hr0,hr1⟩,C.edgePoint_ab r⟩))
  · exact Or.inl (Or.inr ⟨1-r,⟨by linarith,by linarith⟩,by
      rw [C.edgePoint_cd,show 1-(1-r)=r by ring]⟩)

theorem boundary_coordinates (ht : G.TriangleFree) {z : Plane} (hz : z∈C.boundary) :
    z∈C.closedRegion ∧
      (C.coordU z=0 ∨ C.coordU z=1 ∨ C.coordV z=0 ∨ C.coordV z=1) := by
  rcases hz with ((hz | hz) | hz) | hz
  all_goals obtain ⟨t,⟨ht0,ht1⟩,rfl⟩ := hz
  · rw [C.edgePoint_ab]
    simp only [closedRegion,Set.mem_ofPred_eq,C.coordU_cellPoint ht,C.coordV_cellPoint ht]
    exact ⟨⟨ht0,ht1,le_refl _,by norm_num⟩,Or.inr (Or.inr (Or.inl True.intro))⟩
  · rw [C.edgePoint_bc]
    simp only [closedRegion,Set.mem_ofPred_eq,C.coordU_cellPoint ht,C.coordV_cellPoint ht]
    exact ⟨⟨by norm_num,le_refl _,ht0,ht1⟩,Or.inr (Or.inl True.intro)⟩
  · rw [C.edgePoint_cd]
    simp only [closedRegion,Set.mem_ofPred_eq,C.coordU_cellPoint ht,C.coordV_cellPoint ht]
    exact ⟨⟨by linarith,by linarith,by norm_num,le_refl _⟩,Or.inr (Or.inr (Or.inr True.intro))⟩
  · rw [C.edgePoint_da]
    simp only [closedRegion,Set.mem_ofPred_eq,C.coordU_cellPoint ht,C.coordV_cellPoint ht]
    exact ⟨⟨le_refl _,by norm_num,by linarith,by linarith⟩,Or.inl True.intro⟩

theorem boundary_disjoint_openRegion (ht : G.TriangleFree) :
    _root_.Disjoint C.boundary C.openRegion := by
  apply Set.disjoint_left.mpr
  intro z hz ho
  have hb := (C.boundary_coordinates ht hz).2
  rcases ho with ⟨hr0,hr1,hs0,hs1⟩
  rcases hb with h | h | h | h <;> linarith

theorem closedRegion_subset_open_union_boundary (ht : G.TriangleFree) :
    C.closedRegion⊆C.openRegion ∪ C.boundary := by
  rintro z ⟨hr0,hr1,hs0,hs1⟩
  by_cases h0 : 0<C.coordU z
  · by_cases h1 : C.coordU z<1
    · by_cases h2 : 0<C.coordV z
      · by_cases h3 : C.coordV z<1
        · exact Or.inl ⟨h0,h1,h2,h3⟩
        · right
          rw [← C.reconstruct ht z]
          exact C.cellPoint_mem_boundary hr0 hr1 hs0 hs1 (Or.inr (Or.inr (Or.inr (by linarith))))
      · right
        rw [← C.reconstruct ht z]
        exact C.cellPoint_mem_boundary hr0 hr1 hs0 hs1 (Or.inr (Or.inr (Or.inl (by linarith))))
    · right
      rw [← C.reconstruct ht z]
      exact C.cellPoint_mem_boundary hr0 hr1 hs0 hs1 (Or.inr (Or.inl (by linarith)))
  · right
    rw [← C.reconstruct ht z]
    exact C.cellPoint_mem_boundary hr0 hr1 hs0 hs1 (Or.inl (by linarith))

theorem boundary_subset_drawing : C.boundary⊆G.drawing := by
  exact Set.union_subset (Set.union_subset (Set.union_subset
    (G.edgeTrace_subset_drawing _ _ C.ab) (G.edgeTrace_subset_drawing _ _ C.bc))
    (G.edgeTrace_subset_drawing _ _ C.cd)) (G.edgeTrace_subset_drawing _ _ C.da)

theorem point_corner_mem_boundary (i : Fin n) (hi : i∈C.corners) : G.point i∈C.boundary := by
  simp only [corners,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact Or.inl (Or.inl (Or.inl ⟨0,⟨by norm_num,by norm_num⟩,by simp [PennyGraph.edgePoint]⟩))
  · exact Or.inl (Or.inl (Or.inl ⟨1,⟨by norm_num,by norm_num⟩,by simp [PennyGraph.edgePoint]⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨1,⟨by norm_num,by norm_num⟩,by simp [PennyGraph.edgePoint]⟩))
  · exact Or.inr ⟨0,⟨by norm_num,by norm_num⟩,by simp [PennyGraph.edgePoint]⟩

theorem vertex_mem_corners_of_mem_closedRegion (ht : G.TriangleFree) (i : Fin n)
    (hi : G.point i∈C.closedRegion) : i∈C.corners := by
  obtain ⟨hr0,hr1,hs0,hs1⟩ := hi
  have he : G.point i-G.point C.a=C.coordU (G.point i) • C.u+C.coordV (G.point i) • C.v := by
    have hh := C.reconstruct ht (G.point i)
    dsimp [cellPoint] at hh
    calc
      _ = (G.point C.a+C.coordU (G.point i) • C.u+C.coordV (G.point i) • C.v)-G.point C.a :=
        congrArg (fun z : Plane => z-G.point C.a) hh.symm
      _ = _ := by abel
  have hc := C.no_other_vertices i _ _ hr0 hr1 hs0 hs1 he
  simpa only [corners,Finset.mem_insert,Finset.mem_singleton] using hc

theorem vertex_not_mem_openRegion (ht : G.TriangleFree) (i : Fin n) : G.point i∉C.openRegion := by
  intro hi
  have hc := C.vertex_mem_corners_of_mem_closedRegion ht i (C.openRegion_subset_closedRegion hi)
  exact Set.disjoint_left.mp (C.boundary_disjoint_openRegion ht)
    (C.point_corner_mem_boundary i hc) hi

end RhombusCell
end Swanepoel
