module
public import Swanepoel.SpokeBanksAllLoops
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

namespace PentagonSpokeLoops
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} {P : PentagonFaceBoundary G F}
    (K : PentagonSpokeLoops G F P)

theorem rootCode_coordinate (ht : G.TriangleFree)
    {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (hFY : F∈Y)
    (hports : ∀ s∈G.faceSourcePorts F,edgeComponent s∈G.familyBoundaryTrackComponents Y)
    (i j : Fin 5) : K.rootCode j i=
      if j=i+1 then (K.spine i).bankLabel (K.loop i) 1 else (K.spine i).bankLabel (K.loop i) (-1) := by
  have hinj := P.boundary_spoke_component_injective ht hY hFY hports
  have h0 := K.carried_start_bank_label ht i (P.dart i) rfl (-1) (Or.inr rfl)
    (by simp only [neg_neg,one_smul])
  have h1 := K.carried_start_bank_label ht i (reverseEdge (P.dart i))
    (reverse_component (P.dart i)).symm 1 (Or.inl rfl) (by rw [reverseEdge_vector,neg_one_smul])
  have edge (k : Fin 5) (hk0 : k≠i) (hk1 : k≠i+1) :
      (K.loop i).windingIndex (G.point (P.vertex k))=
        (K.loop i).windingIndex (G.point (P.vertex (k+1))) :=
    (K.support i).edge_endpoint_winding_eq ht (P.dart k)
      (fun h => hk0 (hinj h)) (fun h => hk1 (hinj h))
  have h2 := edge (i+2) (by fin_cases i <;> decide) (by fin_cases i <;> decide)
  have h3 := edge (i+3) (by fin_cases i <;> decide) (by fin_cases i <;> decide)
  have h4 := edge (i+4) (by fin_cases i <;> decide) (by fin_cases i <;> decide)
  have hi2 : (i+2)+1=i+3 := by rw [add_assoc]; rfl
  have hi3 : (i+3)+1=i+4 := by rw [add_assoc]; rfl
  have hi4 : (i+4)+1=i := by fin_cases i <;> decide
  rw [hi2] at h2
  rw [hi3] at h3
  rw [hi4] at h4
  change (K.loop i).windingIndex (G.point (P.vertex i))=(K.spine i).bankLabel (K.loop i) (-1) at h0
  change (K.loop i).windingIndex (G.point (P.vertex (i+1)))=(K.spine i).bankLabel (K.loop i) 1 at h1
  change (K.loop i).windingIndex (G.point (P.vertex j))= _
  by_cases hj : j=i+1
  · rw [hj,ite_eq_left rfl]
    exact h1
  · rw [ite_eq_right hj]
    have hcases : j=i ∨ j=i+2 ∨ j=i+3 ∨ j=i+4 := by
      fin_cases i <;> fin_cases j <;> norm_num at *
    rcases hcases with rfl | rfl | rfl | rfl
    · exact h0
    · exact h2.trans (h3.trans (h4.trans h0))
    · exact h3.trans (h4.trans h0)
    · exact h4.trans h0

theorem rootCode_injective (ht : G.TriangleFree)
    {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (hFY : F∈Y)
    (hports : ∀ s∈G.faceSourcePorts F,edgeComponent s∈G.familyBoundaryTrackComponents Y) :
    Function.Injective K.rootCode := by
  intro a b hab
  by_contra hne
  have hi : a=(a+4)+1 := by fin_cases a <;> decide
  have hb : b≠(a+4)+1 := by intro h; exact hne (hi.trans h.symm)
  have h := congrFun hab (a+4)
  rw [K.rootCode_coordinate ht hY hFY hports,K.rootCode_coordinate ht hY hFY hports,
    ite_eq_left hi,ite_eq_right hb] at h
  exact K.bank_labels_distinct (a+4) h

theorem vertexCode_mem_rootCodes (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht)
    (hc : G.graph.Connected) (v : Fin n) : ∃ j : Fin 5,K.vertexCode v=K.rootCode j := by
  have edge (a b : Fin n) (hab : G.graph.Adj a b)
      (ha : ∃ j : Fin 5,K.vertexCode a=K.rootCode j) : ∃ j : Fin 5,K.vertexCode b=K.rootCode j := by
    let e : OrientedEdge G := ⟨(a,b),hab⟩
    by_cases hs : ∃ j : Fin 5,edgeComponent e=edgeComponent (P.dart j)
    · obtain ⟨j,hj⟩ := hs
      have hr := (reverse_component e).symm.trans hj
      rcases K.carried_start_code ht hF j (reverseEdge e) hr with h | h
      · exact ⟨j,h.2⟩
      · exact ⟨j+1,h.2⟩
    · have hn : ∀ j : Fin 5,edgeComponent e≠edgeComponent (P.dart j) :=
        fun j h => hs ⟨j,h⟩
      have heq := K.nonspoke_edge_code_eq ht e hn
      obtain ⟨j,hj⟩ := ha
      exact ⟨j,heq.symm.trans hj⟩
  have walk (a b : Fin n) (p : G.graph.Walk a b) :
      (∃ j : Fin 5,K.vertexCode a=K.rootCode j) → ∃ j : Fin 5,K.vertexCode b=K.rootCode j := by
    induction p with
    | nil => exact id
    | @cons a b c hab p ih => intro ha; exact ih (edge a b hab ha)
  obtain ⟨p⟩ := hc.preconnected (P.vertex 0) v
  exact walk _ _ p ⟨0,rfl⟩

theorem defectCode_exists_unique (ht : G.TriangleFree) (hc : G.graph.Connected)
    {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (hFY : F∈Y)
    (hports : ∀ s∈G.faceSourcePorts F,edgeComponent s∈G.familyBoundaryTrackComponents Y)
    (H : PlaneFace G) (hH : H∈G.defectPlaneFaces ht) (hHF : H≠F) :
    ∃! j : Fin 5,K.code H=K.rootCode j := by
  have hm := G.defect_source_ports_five_le ht H hH
  obtain ⟨e,he⟩ := Finset.card_pos.mp (show 0<(G.faceSourcePorts H).card by omega)
  have heH := (Finset.mem_filter.mp he).2.2
  have hclosure := (G.sourceFace_endpoints_mem_closure e).1
  rw [heH] at hclosure
  have hcode : K.vertexCode e.val.1=K.code H := by
    funext i
    exact (K.support i).defect_vertex_winding_label ht K.outer_unbounded H hH hHF _ hclosure
  obtain ⟨j,hj⟩ := K.vertexCode_mem_rootCodes ht (hY.subset_defects hFY) hc e.val.1
  have hface := hcode.symm.trans hj
  refine ⟨j,hface,?_⟩
  intro k hk
  exact K.rootCode_injective ht hY hFY hports (hk.symm.trans hface)

def codeSector (code : Fin 5→ℤ) : Fin 5 :=
  if h : ∃ j : Fin 5,code=K.rootCode j then Classical.choose h else 0

theorem codeSector_root (ht : G.TriangleFree)
    {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (hFY : F∈Y)
    (hports : ∀ s∈G.faceSourcePorts F,edgeComponent s∈G.familyBoundaryTrackComponents Y)
    (j : Fin 5) : K.codeSector (K.rootCode j)=j := by
  have h : ∃ k : Fin 5,K.rootCode j=K.rootCode k := ⟨j,rfl⟩
  rw [codeSector,dite_eq_left h]
  exact (K.rootCode_injective ht hY hFY hports (Classical.choose_spec h)).symm

def vertexSector (v : Fin n) : Fin 5 := K.codeSector (K.vertexCode v)
def faceSector (H : PlaneFace G) : Fin 5 := K.codeSector (K.code H)

theorem vertexCode_eq_root_sector (ht : G.TriangleFree) (hc : G.graph.Connected)
    {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (hFY : F∈Y)
    (hports : ∀ s∈G.faceSourcePorts F,edgeComponent s∈G.familyBoundaryTrackComponents Y)
    (v : Fin n) : K.vertexCode v=K.rootCode (K.vertexSector v) := by
  obtain ⟨j,hj⟩ := K.vertexCode_mem_rootCodes ht (hY.subset_defects hFY) hc v
  unfold vertexSector
  rw [hj,K.codeSector_root ht hY hFY hports]

theorem defectCode_eq_root_sector (ht : G.TriangleFree) (hc : G.graph.Connected)
    {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (hFY : F∈Y)
    (hports : ∀ s∈G.faceSourcePorts F,edgeComponent s∈G.familyBoundaryTrackComponents Y)
    (H : PlaneFace G) (hH : H∈G.defectPlaneFaces ht) (hHF : H≠F) :
    K.code H=K.rootCode (K.faceSector H) := by
  obtain ⟨j,hj,_⟩ := K.defectCode_exists_unique ht hc hY hFY hports H hH hHF
  unfold faceSector
  rw [hj,K.codeSector_root ht hY hFY hports]

end PentagonSpokeLoops
end Swanepoel
