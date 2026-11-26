module
public import Swanepoel.EdgeFacePreservation
@[expose] public section

noncomputable section
namespace Swanepoel

def PennyGraph.IsSubFace {n : ℕ} (G : PennyGraph n) (S : Finset (ContactEdge G)) (F : Set Plane) : Prop :=
  ∃ x∈(G.subdrawing S)ᶜ, F=connectedComponentIn (G.subdrawing S)ᶜ x

def PennyGraph.subdrawingFaces {n : ℕ} (G : PennyGraph n) (S : Finset (ContactEdge G)) : Set (Set Plane) :=
  {F | G.IsSubFace S F}

abbrev ContactFace {n : ℕ} (G : PennyGraph n) (S : Finset (ContactEdge G)) :=
  {F : Set Plane // G.IsSubFace S F}

theorem PennyGraph.IsSubFace.isOpen {n : ℕ} {G : PennyGraph n} {S : Finset (ContactEdge G)}
    {F : Set Plane} (hf : G.IsSubFace S F) : IsOpen F := by
  obtain ⟨x,_,rfl⟩ := hf
  exact (G.isCompact_subdrawing S).isClosed.isOpen_compl.connectedComponentIn

theorem PennyGraph.IsSubFace.nonempty {n : ℕ} {G : PennyGraph n} {S : Finset (ContactEdge G)}
    {F : Set Plane} (hf : G.IsSubFace S F) : F.Nonempty := by
  obtain ⟨x,hx,rfl⟩ := hf
  exact ⟨x,mem_connectedComponentIn hx⟩

theorem PennyGraph.IsSubFace.eq_component {n : ℕ} {G : PennyGraph n} {S : Finset (ContactEdge G)}
    {F : Set Plane} (hf : G.IsSubFace S F) {x : Plane} (hx : x∈F) :
    F=connectedComponentIn (G.subdrawing S)ᶜ x := by
  obtain ⟨y,_,rfl⟩ := hf
  exact connectedComponentIn_eq hx

theorem PennyGraph.subdrawing_subset_drawing {n : ℕ} (G : PennyGraph n) (S : Finset (ContactEdge G)) :
    G.subdrawing S⊆G.drawing := by
  rintro z (hp | he)
  · exact Or.inl hp
  · obtain ⟨e,he⟩ := Set.mem_iUnion.mp he
    obtain ⟨_,he⟩ := Set.mem_iUnion.mp he
    exact Or.inr (Set.mem_iUnion.mpr ⟨⟨e.val,e.property.2⟩,he⟩)

theorem PennyGraph.dense_complement_drawing {n : ℕ} (G : PennyGraph n) : Dense G.drawingᶜ := by
  have hd := dense_finite_intersection
    (fun i : Fin n ⊕ OrientedEdge G => {z : Plane | G.coverForm i z≠G.coverLevel i})
    (fun i => isOpen_ne.preimage (G.coverForm i).continuous_of_finiteDimensional)
    (fun i => dense_complement_affine_line (G.coverForm i) (G.coverForm_ne_zero i) (G.coverLevel i))
  apply hd.mono
  intro z hz hzD
  obtain ⟨i,hi⟩ := G.drawing_affine_cover z hzD
  exact (Set.mem_iInter.mp hz i) hi

instance contactFaceFinite {n : ℕ} (G : PennyGraph n) (S : Finset (ContactEdge G)) :
    Finite (ContactFace G S) := by
  classical
  have hpoint (F : ContactFace G S) : ∃ x, x∈G.drawingᶜ ∧ x∈F.val :=
    G.dense_complement_drawing.exists_mem_open F.property.isOpen F.property.nonempty
  choose p hpFull hpFace using hpoint
  let f (F : ContactFace G S) : PlaneFace G :=
    ⟨connectedComponentIn G.drawingᶜ (p F),⟨p F,hpFull F,rfl⟩⟩
  apply Finite.of_injective f
  intro F H h
  have heq : connectedComponentIn G.drawingᶜ (p F)=connectedComponentIn G.drawingᶜ (p H) :=
    congrArg Subtype.val h
  have hpH : p H∈connectedComponentIn G.drawingᶜ (p F) := by
    rw [heq]
    exact mem_connectedComponentIn (hpFull H)
  have hsub : connectedComponentIn G.drawingᶜ (p F)⊆(G.subdrawing S)ᶜ := by
    intro z hz hdraw
    exact (connectedComponentIn_subset _ _ hz) (G.subdrawing_subset_drawing S hdraw)
  have hh := isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (mem_connectedComponentIn (hpFull F)) hsub hpH
  apply Subtype.ext
  exact (F.property.eq_component (hpFace F)).trans
    ((connectedComponentIn_eq hh).trans (H.property.eq_component (hpFace H)).symm)

theorem PennyGraph.subdrawingFaces_finite {n : ℕ} (G : PennyGraph n) (S : Finset (ContactEdge G)) :
    (G.subdrawingFaces S).Finite := by
  apply Set.finite_coe_iff.mp
  change Finite (ContactFace G S)
  infer_instance

theorem PennyGraph.subdrawingFaces_insert {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) (he : e∉S) :
    G.subdrawingFaces (insert e S)=
      (G.subdrawingFaces S \ {connectedComponentIn (G.subdrawing S)ᶜ (G.edgePoint e.val.1 e.val.2 (1/2))}) ∪
      {connectedComponentIn (G.subdrawing (insert e S))ᶜ (G.edgeSidePoint S e true (1/2)),
       connectedComponentIn (G.subdrawing (insert e S))ᶜ (G.edgeSidePoint S e false (1/2))} := by
  classical
  ext F
  constructor
  · rintro ⟨x,hx,rfl⟩
    have hxOld : x∈(G.subdrawing S)ᶜ := by
      intro hdraw
      exact hx (by rw [G.subdrawing_insert]; exact Or.inl hdraw)
    by_cases hxU : x∈connectedComponentIn (G.subdrawing S)ᶜ (G.edgePoint e.val.1 e.val.2 (1/2))
    · right
      rcases G.insert_edge_at_most_two_components S e he hxU hx with h | h
      · exact Or.inl h
      · exact Or.inr (Set.mem_singleton_iff.mpr h)
    · left
      have hc := G.insert_edge_other_component_unchanged S e he hxOld hxU
      refine ⟨⟨x,hxOld,hc⟩,?_⟩
      intro hsame
      have heq := Set.mem_singleton_iff.mp hsame
      have hxC := mem_connectedComponentIn hx
      exact hxU (heq ▸ hxC)
  · rintro (⟨hF,hNot⟩ | hF)
    · obtain ⟨x,hx,rfl⟩ := hF
      have hxNot : x∉connectedComponentIn (G.subdrawing S)ᶜ (G.edgePoint e.val.1 e.val.2 (1/2)) := by
        intro hxU
        exact hNot (Set.mem_singleton_iff.mpr (connectedComponentIn_eq hxU).symm)
      have hc := G.insert_edge_other_component_unchanged S e he hx hxNot
      have hxNew : x∈(G.subdrawing (insert e S))ᶜ := by
        apply connectedComponentIn_subset _ _
        rw [hc]
        exact mem_connectedComponentIn hx
      exact ⟨x,hxNew,hc.symm⟩
    · rcases hF with hF | hF
      · rw [hF]
        exact ⟨G.edgeSidePoint S e true (1/2),
          G.edgeSidePoint_mem_complement S e he true (by norm_num) (by norm_num),rfl⟩
      · rw [Set.mem_singleton_iff.mp hF]
        exact ⟨G.edgeSidePoint S e false (1/2),
          G.edgeSidePoint_mem_complement S e he false (by norm_num) (by norm_num),rfl⟩

end Swanepoel
