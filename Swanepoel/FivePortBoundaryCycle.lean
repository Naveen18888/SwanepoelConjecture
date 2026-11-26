module
public import Swanepoel.FaceBoundaryCapReduction
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace FaceBoundaryCycle
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} {initial : OrientedEdge G}
    (C : FaceBoundaryCycle G F initial)

def dartSet : Finset (OrientedEdge G) :=
  Finset.univ.image (fun i : Fin C.length => C.edge i.castSucc)

theorem dartSet_card : C.dartSet.card=C.length := by
  rw [dartSet,Finset.card_image_of_injective _ C.edge_injective,Finset.card_univ,Fintype.card_fin]

theorem dartSet_subset_ports (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht) :
    C.dartSet ⊆ G.faceSourcePorts F := by
  intro e he
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
  exact C.port_membership ht hF i

theorem dartSet_normal_sum : (∑ e∈C.dartSet,sourceNormal e)=0 := by
  rw [dartSet,Finset.sum_image (by
    intro i _ j _ h
    exact C.edge_injective h)]
  exact C.normal_sum

theorem length_ne_three (ht : G.TriangleFree) : C.length≠3 := by
  intro h3
  have h01 := C.vertexAt_contact 0 (by omega)
  have h12 := C.vertexAt_contact 1 (by omega)
  have h20 := C.vertexAt_contact 2 (by omega)
  have hclose : C.vertexAt 3=C.vertexAt 0 := by simpa only [h3] using C.vertexAt_closes
  rw [hclose] at h20
  exact ht _ _ _ h01 h12 h20

theorem ports_sdiff_dartSet_card_ne_one (ht : G.TriangleFree)
    (hF : F∈G.defectPlaneFaces ht) :
    (G.faceSourcePorts F \ C.dartSet).card≠1 := by
  intro hone
  obtain ⟨e,he⟩ := Finset.card_eq_one.mp hone
  have hsum := Finset.sum_sdiff (f := sourceNormal) (C.dartSet_subset_ports ht hF)
  rw [he,Finset.sum_singleton,C.dartSet_normal_sum,
    G.defect_all_source_normals_sum ht F hF,add_zero] at hsum
  have hn := sourceNormal_norm e
  rw [hsum,norm_zero] at hn
  norm_num at hn

theorem length_eq_five_of_five_ports (ht : G.TriangleFree)
    (hF : F∈G.defectPlaneFaces ht)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (hfive : (G.faceSourcePorts F).card=5) :
    C.length=5 ∧ C.dartSet=G.faceSourcePorts F := by
  have hsub := C.dartSet_subset_ports ht hF
  have hcard := Finset.card_le_card hsub
  rw [C.dartSet_card,hfive] at hcard
  have hthree := C.three_le_length hdegree
  have hne3 := C.length_ne_three ht
  have hne4 : C.length≠4 := by
    intro h4
    have hrem : (G.faceSourcePorts F \ C.dartSet).card=1 := by
      rw [Finset.card_sdiff_of_subset hsub,hfive,C.dartSet_card,h4]
    exact C.ports_sdiff_dartSet_card_ne_one ht hF hrem
  have hL : C.length=5 := by omega
  refine ⟨hL,Finset.eq_of_subset_of_card_le hsub ?_⟩
  rw [C.dartSet_card,hL,hfive]

end FaceBoundaryCycle

theorem PennyGraph.five_port_defect_coherent_cycle {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (hF : F∈G.defectPlaneFaces ht)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (hfive : (G.faceSourcePorts F).card=5) :
    ∃ initial : OrientedEdge G, ∃ C : FaceBoundaryCycle G F initial,
      C.length=5 ∧ C.dartSet=G.faceSourcePorts F := by
  have hne : (G.faceSourcePorts F).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨initial,hinitial⟩ := hne
  have hface : G.sourceFace initial=F := (Finset.mem_filter.mp hinitial).2.2
  obtain ⟨C⟩ := G.minimal_face_boundary_cycle F initial hface
  exact ⟨initial,C,C.length_eq_five_of_five_ports ht hF hdegree hfive⟩

end Swanepoel
