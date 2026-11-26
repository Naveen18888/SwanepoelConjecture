module
public import Swanepoel.ContactFaces
public import Mathlib.Data.Set.Card
@[expose] public section

noncomputable section
namespace Swanepoel

theorem PennyGraph.subdrawing_face_count_insert {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) (he : e∉S) :
    (G.subdrawingFaces (insert e S)).ncard=(G.subdrawingFaces S).ncard+
      (if connectedComponentIn (G.subdrawing (insert e S))ᶜ (G.edgeSidePoint S e true (1/2))=
          connectedComponentIn (G.subdrawing (insert e S))ᶜ (G.edgeSidePoint S e false (1/2))
        then 0 else 1) := by
  classical
  let U := connectedComponentIn (G.subdrawing S)ᶜ (G.edgePoint e.val.1 e.val.2 (1/2))
  let L := connectedComponentIn (G.subdrawing (insert e S))ᶜ (G.edgeSidePoint S e true (1/2))
  let R := connectedComponentIn (G.subdrawing (insert e S))ᶜ (G.edgeSidePoint S e false (1/2))
  have hU : U∈G.subdrawingFaces S := by
    refine ⟨G.edgePoint e.val.1 e.val.2 (1/2),?_,rfl⟩
    exact Set.disjoint_left.mp (G.omitted_edge_disjoint_subdrawing S e he)
      ⟨1/2,⟨by norm_num,by norm_num⟩,rfl⟩
  have hNot (left : Bool) :
      connectedComponentIn (G.subdrawing (insert e S))ᶜ (G.edgeSidePoint S e left (1/2))∉
        G.subdrawingFaces S \ {U} := by
    rintro ⟨hf,hneq⟩
    have hp := G.edgeSidePoint_mem_complement S e he left (t := 1/2) (by norm_num) (by norm_num)
    have hpC := mem_connectedComponentIn hp
    have hpU := G.edge_side_component_subset_old_face S e he left hpC
    have hf' : G.IsSubFace S
        (connectedComponentIn (G.subdrawing (insert e S))ᶜ (G.edgeSidePoint S e left (1/2))) := hf
    have heq := (hf'.eq_component hpC).trans (connectedComponentIn_eq hpU).symm
    exact hneq (Set.mem_singleton_iff.mpr heq)
  have hdis : _root_.Disjoint (G.subdrawingFaces S \ {U}) ({L,R} : Set (Set Plane)) := by
    apply Set.disjoint_right.mpr
    intro F hF hold
    rcases hF with hF | hF
    · rw [hF] at hold
      exact hNot true hold
    · rw [Set.mem_singleton_iff.mp hF] at hold
      exact hNot false hold
  have hreplace : G.subdrawingFaces (insert e S)=(G.subdrawingFaces S \ {U}) ∪ {L,R} :=
    G.subdrawingFaces_insert S e he
  have hcut := Set.ncard_sdiff_singleton_add_one hU (G.subdrawingFaces_finite S)
  change (G.subdrawingFaces (insert e S)).ncard=(G.subdrawingFaces S).ncard+(if L=R then 0 else 1)
  rw [hreplace,Set.ncard_union_eq hdis
    ((G.subdrawingFaces_finite S).subset Set.sdiff_subset) ((Set.finite_singleton R).insert L)]
  by_cases hLR : L=R
  · simp only [hLR,Set.pair_eq_singleton,Set.ncard_singleton,ite_true]
    omega
  · rw [Set.ncard_pair hLR,ite_eq_right hLR]
    omega

end Swanepoel
