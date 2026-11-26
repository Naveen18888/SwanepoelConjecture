module
public import Swanepoel.FacePortIncidence
public import Swanepoel.EulerStart
public import Swanepoel.OuterFace
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def PennyGraph.faceDualGraph {n : ℕ} (G : PennyGraph n) : SimpleGraph (PlaneFace G) where
  Adj F H := F ≠ H ∧ ∃ e : OrientedEdge G,
    G.sourceFace e = F ∧ G.sourceFace (reverseEdge e) = H
  symm := ⟨by
    rintro F H ⟨hne,e,he,hr⟩
    refine ⟨hne.symm,reverseEdge e,hr,?_⟩
    simpa only [reverseEdge_involutive] using he⟩
  loopless := ⟨by rintro F ⟨hne,_⟩; exact hne rfl⟩

def PennyGraph.faceDualRegion {n : ℕ} (G : PennyGraph n) (P : PlaneFace G → Prop) : Set Plane :=
  {z | ∃ F : PlaneFace G, P F ∧ z ∈ F.val} ∪
    {z | ∃ e : ContactEdge G, P (G.sourceFace e.forwardEdge) ∧ z ∈ G.openEdgeTrace e.val.1 e.val.2}

theorem PennyGraph.faceDualRegion_isOpen {n : ℕ} (G : PennyGraph n)
    (P : PlaneFace G → Prop)
    (hinvariant : ∀ e : ContactEdge G,
      P (G.sourceFace e.forwardEdge) ↔ P (G.sourceFace (reverseEdge e.forwardEdge))) :
    IsOpen (G.faceDualRegion P) := by
  apply Metric.isOpen_iff.mpr
  intro z hz
  rcases hz with ⟨F,hPF,hzF⟩ | ⟨e,hPe,t,⟨ht0,ht1⟩,rfl⟩
  · obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp F.property.isOpen z hzF
    exact ⟨r,hr,fun y hy => Or.inl ⟨F,hPF,hball hy⟩⟩
  · let S : Finset (ContactEdge G) := Finset.univ.erase e
    have he : e ∉ S := Finset.notMem_erase _ _
    have hdrawing : G.subdrawing (insert e S) = G.drawing := by
      simp only [S,Finset.insert_erase (Finset.mem_univ _),G.subdrawing_univ]
    have hspec := G.edgeClearance_spec S e he ht0 ht1
    have hfree : Metric.ball (G.edgePoint e.val.1 e.val.2 t) (2*G.edgeClearance S e t) ⊆
        (G.subdrawing S)ᶜ :=
      (Metric.ball_subset_ball hspec.2.2.2.le).trans Metric.ball_infDist_subset_compl
    have hlocal := G.edgeClearance_ball_complement S e he ht0 ht1
    have hsides := G.edge_sides_in_fixed_components S e he ht0 ht1
    rw [hdrawing] at hlocal hsides
    have hleft : P (G.sourceFace (reverseEdge e.forwardEdge)) := (hinvariant e).mp hPe
    refine ⟨2*G.edgeClearance S e t,by have hδ := hspec.1; positivity,?_⟩
    intro y hy
    by_cases hydraw : y ∈ G.drawing
    · have hyedge : y ∈ G.openEdgeTrace e.val.1 e.val.2 := by
        rw [← hdrawing,G.subdrawing_insert_open] at hydraw
        exact hydraw.resolve_left (hfree hy)
      exact Or.inr ⟨e,hPe,hyedge⟩
    · have hysides : y ∈
          leftHalfBall (G.point e.val.2-G.point e.val.1) (G.edgePoint e.val.1 e.val.2 t)
            (2*G.edgeClearance S e t) ∪
          rightHalfBall (G.point e.val.2-G.point e.val.1) (G.edgePoint e.val.1 e.val.2 t)
            (2*G.edgeClearance S e t) := by
        rw [← hlocal]
        exact ⟨hy,hydraw⟩
      rcases hysides with hyL | hyR
      · have hyface := hsides.1 hyL
        rw [G.contact_left_component_eq_sourceFace] at hyface
        exact Or.inl ⟨G.sourceFace (reverseEdge e.forwardEdge),hleft,hyface⟩
      · have hyface := hsides.2 hyR
        rw [G.contact_right_component_eq_sourceFace] at hyface
        exact Or.inl ⟨G.sourceFace e.forwardEdge,hPe,hyface⟩

theorem PennyGraph.faceDualRegions_disjoint {n : ℕ} (G : PennyGraph n)
    (P : PlaneFace G → Prop) :
    Disjoint (G.faceDualRegion P) (G.faceDualRegion (fun F => ¬ P F)) := by
  apply Set.disjoint_left.mpr
  intro z hzP hzN
  rcases hzP with ⟨F,hPF,hzF⟩ | ⟨e,hPe,t,⟨ht0,ht1⟩,rfl⟩
  · rcases hzN with ⟨H,hNH,hzH⟩ | ⟨e,hNe,t,⟨ht0,ht1⟩,hparam⟩
    · have hFH : F = H := Subtype.ext ((F.property.eq_component hzF).trans
        (H.property.eq_component hzH).symm)
      exact hNH (hFH ▸ hPF)
    · exact G.face_subset_complement F hzF (G.edgeTrace_subset_drawing _ _ e.property.2
        ⟨t,⟨ht0.le,ht1.le⟩,hparam⟩)
  · rcases hzN with ⟨H,hNH,hzH⟩ | ⟨f,hNf,s,⟨hs0,hs1⟩,hparam⟩
    · exact G.face_subset_complement H hzH (G.edgeTrace_subset_drawing _ _ e.property.2
        ⟨t,⟨ht0.le,ht1.le⟩,rfl⟩)
    · have hunordered := G.interior_edge_intersection _ _ _ _ e.property.2 f.property.2
        ht0 ht1 hs0.le hs1.le hparam.symm
      have hef := e.eq_of_unordered_eq f hunordered
      exact hNf (hef ▸ hPe)

theorem PennyGraph.faceDualRegion_cover_complement_vertices {n : ℕ} (G : PennyGraph n)
    (P : PlaneFace G → Prop) :
    (Set.range G.point)ᶜ ⊆ G.faceDualRegion P ∪ G.faceDualRegion (fun F => ¬ P F) := by
  intro z hz
  by_cases hzdraw : z ∈ G.drawing
  · have hzsub : z ∈ G.subdrawing Finset.univ := by rwa [G.subdrawing_univ]
    rcases hzsub with hzpoint | hzedge
    · exact False.elim (hz hzpoint)
    · obtain ⟨e,he⟩ := Set.mem_iUnion.mp hzedge
      obtain ⟨_,t,⟨ht0,ht1⟩,hparam⟩ := Set.mem_iUnion.mp he
      have hne0 : t ≠ 0 := by
        intro ht
        apply hz
        exact ⟨e.val.1,by simpa [PennyGraph.edgePoint,ht] using hparam⟩
      have hne1 : t ≠ 1 := by
        intro ht
        apply hz
        exact ⟨e.val.2,by simpa [PennyGraph.edgePoint,ht] using hparam⟩
      have hopen : z ∈ G.openEdgeTrace e.val.1 e.val.2 :=
        ⟨t,⟨lt_of_le_of_ne ht0 (Ne.symm hne0),lt_of_le_of_ne ht1 hne1⟩,hparam⟩
      by_cases hP : P (G.sourceFace e.forwardEdge)
      · exact Or.inl (Or.inr ⟨e,hP,hopen⟩)
      · exact Or.inr (Or.inr ⟨e,hP,hopen⟩)
  · let F : PlaneFace G := ⟨connectedComponentIn G.drawingᶜ z,⟨z,hzdraw,rfl⟩⟩
    have hzF : z ∈ F.val := mem_connectedComponentIn hzdraw
    by_cases hP : P F
    · exact Or.inl (Or.inl ⟨F,hP,hzF⟩)
    · exact Or.inr (Or.inl ⟨F,hP,hzF⟩)

theorem PennyGraph.face_predicate_constant_of_edge_invariant {n : ℕ} (G : PennyGraph n)
    (P : PlaneFace G → Prop)
    (hinvariant : ∀ e : ContactEdge G,
      P (G.sourceFace e.forwardEdge) ↔ P (G.sourceFace (reverseEdge e.forwardEdge)))
    (F : PlaneFace G) (hPF : P F) : ∀ H : PlaneFace G, P H := by
  let X := (Set.range G.point)ᶜ
  have hX : IsConnected X := by
    simpa only [PennyGraph.subdrawing_empty] using G.empty_subdrawing_complement_connected
  have hU := G.faceDualRegion_isOpen P hinvariant
  have hV := G.faceDualRegion_isOpen (fun H => ¬ P H) (fun e => not_congr (hinvariant e))
  have hdis := G.faceDualRegions_disjoint P
  have hcover := G.faceDualRegion_cover_complement_vertices P
  obtain ⟨x,hxF⟩ := F.property.nonempty
  have hxX : x ∈ X := by
    rintro ⟨i,hi⟩
    exact G.face_subset_complement F hxF (hi ▸ G.point_mem_drawing i)
  have hxU : x ∈ G.faceDualRegion P := Or.inl ⟨F,hPF,hxF⟩
  have hXU : X ⊆ G.faceDualRegion P := hX.isPreconnected.subset_left_of_subset_union
    hU hV hdis hcover ⟨x,hxX,hxU⟩
  intro H
  obtain ⟨y,hyH⟩ := H.property.nonempty
  have hyX : y ∈ X := by
    rintro ⟨i,hi⟩
    exact G.face_subset_complement H hyH (hi ▸ G.point_mem_drawing i)
  rcases hXU hyX with ⟨K,hPK,hyK⟩ | ⟨e,hPe,t,⟨ht0,ht1⟩,hparam⟩
  · have hKH : K = H := Subtype.ext ((K.property.eq_component hyK).trans
      (H.property.eq_component hyH).symm)
    exact hKH ▸ hPK
  · exact False.elim (G.face_subset_complement H hyH (G.edgeTrace_subset_drawing _ _ e.property.2
      ⟨t,⟨ht0.le,ht1.le⟩,hparam⟩))

theorem PennyGraph.faceDualGraph_preconnected {n : ℕ} (G : PennyGraph n) :
    G.faceDualGraph.Preconnected := by
  intro F H
  let P (K : PlaneFace G) := G.faceDualGraph.Reachable F K
  have hinvariant (e : ContactEdge G) :
      P (G.sourceFace e.forwardEdge) ↔ P (G.sourceFace (reverseEdge e.forwardEdge)) := by
    by_cases heq : G.sourceFace e.forwardEdge = G.sourceFace (reverseEdge e.forwardEdge)
    · rw [heq]
    · have hadj : G.faceDualGraph.Adj (G.sourceFace e.forwardEdge)
          (G.sourceFace (reverseEdge e.forwardEdge)) := ⟨heq,e.forwardEdge,rfl,rfl⟩
      exact ⟨fun hr => hr.trans hadj.reachable,fun hr => hr.trans hadj.symm.reachable⟩
  exact G.face_predicate_constant_of_edge_invariant P hinvariant F ⟨SimpleGraph.Walk.nil⟩ H

theorem PennyGraph.faceDualGraph_connected {n : ℕ} (G : PennyGraph n) :
    G.faceDualGraph.Connected := by
  obtain ⟨F,_,_⟩ := G.exists_unique_outer_face
  exact {preconnected := G.faceDualGraph_preconnected,nonempty := ⟨F⟩}

theorem PennyGraph.face_reachable_to_outer {n : ℕ} (G : PennyGraph n) (F : PlaneFace G) :
    ∃ H : PlaneFace G, ¬ Bornology.IsBounded H.val ∧ G.faceDualGraph.Reachable F H := by
  obtain ⟨H,hH,_⟩ := G.exists_unique_outer_face
  exact ⟨H,hH,G.faceDualGraph_connected F H⟩

theorem PennyGraph.face_values_constant_of_edge_agreement {n : ℕ} (G : PennyGraph n)
    {A : Type*} (value : PlaneFace G → A)
    (hagree : ∀ e : OrientedEdge G, value (G.sourceFace e) = value (G.sourceFace (reverseEdge e)))
    (F H : PlaneFace G) : value F = value H := by
  have hinvariant (e : ContactEdge G) :
      (value (G.sourceFace e.forwardEdge) = value F) ↔
        value (G.sourceFace (reverseEdge e.forwardEdge)) = value F := by rw [hagree e.forwardEdge]
  exact (G.face_predicate_constant_of_edge_invariant (fun K => value K = value F)
    hinvariant F rfl H).symm

end Swanepoel
