module
public import Swanepoel.EdgeFaceSplit
@[expose] public section

noncomputable section
namespace Swanepoel

theorem PennyGraph.subdrawing_insert_open {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) :
    G.subdrawing (insert e S)=G.subdrawing S ∪ G.openEdgeTrace e.val.1 e.val.2 := by
  classical
  rw [G.subdrawing_insert]
  ext z
  constructor
  · rintro (hold | ⟨t,⟨ht0,ht1⟩,rfl⟩)
    · exact Or.inl hold
    · by_cases h0 : t=0
      · left
        rw [h0]
        exact Or.inl ⟨e.val.1,by simp [PennyGraph.edgePoint]⟩
      by_cases h1 : t=1
      · left
        rw [h1]
        exact Or.inl ⟨e.val.2,by simp [PennyGraph.edgePoint]⟩
      · exact Or.inr ⟨t,⟨lt_of_le_of_ne ht0 (by intro h; exact h0 h.symm),lt_of_le_of_ne ht1 h1⟩,rfl⟩
  · rintro (hold | ⟨t,⟨ht0,ht1⟩,rfl⟩)
    · exact Or.inl hold
    · exact Or.inr ⟨t,⟨ht0.le,ht1.le⟩,rfl⟩

theorem PennyGraph.insert_edge_other_component_unchanged {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) (he : e∉S) {x : Plane}
    (hx : x∈(G.subdrawing S)ᶜ)
    (hxNot : x∉connectedComponentIn (G.subdrawing S)ᶜ (G.edgePoint e.val.1 e.val.2 (1/2))) :
    connectedComponentIn (G.subdrawing (insert e S))ᶜ x=connectedComponentIn (G.subdrawing S)ᶜ x := by
  let U := connectedComponentIn (G.subdrawing S)ᶜ (G.edgePoint e.val.1 e.val.2 (1/2))
  let C := connectedComponentIn (G.subdrawing S)ᶜ x
  have hCU : ∀ z∈C, z∉U := by
    intro z hz hzU
    have heq : C=U := (connectedComponentIn_eq hz).trans (connectedComponentIn_eq hzU).symm
    have hxC : x∈C := mem_connectedComponentIn hx
    have hxU : x∈U := heq ▸ hxC
    exact hxNot hxU
  have hCnew : C⊆(G.subdrawing (insert e S))ᶜ := by
    intro z hz hnew
    rw [G.subdrawing_insert_open] at hnew
    rcases hnew with hold | hopen
    · exact (connectedComponentIn_subset _ _ hz) hold
    · exact hCU z hz (G.omitted_edge_in_one_face S e he hopen)
  have hxNew := hCnew (mem_connectedComponentIn hx)
  apply Set.Subset.antisymm
  · apply isPreconnected_connectedComponentIn.subset_connectedComponentIn (mem_connectedComponentIn hxNew)
    intro z hz hold
    have hzNew := connectedComponentIn_subset _ _ hz
    exact hzNew (by rw [G.subdrawing_insert]; exact Or.inl hold)
  · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn (mem_connectedComponentIn hx) hCnew

theorem PennyGraph.edge_side_component_subset_old_face {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) (he : e∉S) (left : Bool) :
    connectedComponentIn (G.subdrawing (insert e S))ᶜ (G.edgeSidePoint S e left (1/2)) ⊆
      connectedComponentIn (G.subdrawing S)ᶜ (G.edgePoint e.val.1 e.val.2 (1/2)) := by
  have hs := G.edgeClearance_spec S e he (t := 1/2) (by norm_num) (by norm_num)
  have hu : ‖G.point e.val.2-G.point e.val.1‖=1 := by
    simpa only [← dist_eq_norm] using e.property.2.symm.2
  have hmem := normal_offset_mem_halfBalls _ (G.edgePoint e.val.1 e.val.2 (1/2)) hu hs.1
  have hball : Metric.ball (G.edgePoint e.val.1 e.val.2 (1/2)) (2*G.edgeClearance S e (1/2))⊆
      (G.subdrawing S)ᶜ :=
    (Metric.ball_subset_ball hs.2.2.2.le).trans Metric.ball_infDist_subset_compl
  have hgBall : G.edgeSidePoint S e left (1/2)∈
      Metric.ball (G.edgePoint e.val.1 e.val.2 (1/2)) (2*G.edgeClearance S e (1/2)) := by
    cases left
    · exact hmem.2.1
    · exact hmem.1.1
  have hgOld := (convex_ball _ _).isPreconnected.subset_connectedComponentIn
    (Metric.mem_ball_self (by linarith : 0<2*G.edgeClearance S e (1/2))) hball hgBall
  have hgNew := G.edgeSidePoint_mem_complement S e he left (t := 1/2) (by norm_num) (by norm_num)
  rw [connectedComponentIn_eq hgOld]
  apply isPreconnected_connectedComponentIn.subset_connectedComponentIn (mem_connectedComponentIn hgNew)
  intro z hz hold
  exact (connectedComponentIn_subset _ _ hz) (by rw [G.subdrawing_insert]; exact Or.inl hold)

theorem PennyGraph.insert_edge_old_face_eq_side_union {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) (he : e∉S) :
    connectedComponentIn (G.subdrawing S)ᶜ (G.edgePoint e.val.1 e.val.2 (1/2)) ∩
        (G.subdrawing (insert e S))ᶜ=
      connectedComponentIn (G.subdrawing (insert e S))ᶜ (G.edgeSidePoint S e true (1/2)) ∪
      connectedComponentIn (G.subdrawing (insert e S))ᶜ (G.edgeSidePoint S e false (1/2)) := by
  ext x
  constructor
  · rintro ⟨hxOld,hxNew⟩
    have hx := mem_connectedComponentIn hxNew
    rcases G.insert_edge_at_most_two_components S e he hxOld hxNew with h | h
    · exact Or.inl (h ▸ hx)
    · exact Or.inr (h ▸ hx)
  · rintro (hx | hx)
    · exact ⟨G.edge_side_component_subset_old_face S e he true hx,connectedComponentIn_subset _ _ hx⟩
    · exact ⟨G.edge_side_component_subset_old_face S e he false hx,connectedComponentIn_subset _ _ hx⟩

end Swanepoel
