module
public import Swanepoel.FaceBoundaryPermutation
public import Swanepoel.FaceDualConnectivityLinear
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def PennyGraph.orientedPhysicalEquiv {n : ℕ} (G : PennyGraph n) :
    OrientedEdge G ≃ ContactEdge G × Bool where
  toFun e := (physicalEdge e,sourceProbeSide e)
  invFun p := if p.2 then reverseEdge p.1.forwardEdge else p.1.forwardEdge
  left_inv e := by
    by_cases h : e.val.1 < e.val.2
    · have hnot : ¬ e.val.2 < e.val.1 := not_lt_of_ge h.le
      apply Subtype.ext
      simp [physicalEdge,sourceProbeSide,h,hnot,ContactEdge.forwardEdge]
    · have hgt : e.val.2 < e.val.1 := lt_of_le_of_ne (le_of_not_gt h) e.property.ne.symm
      apply Subtype.ext
      simp [physicalEdge,sourceProbeSide,h,hgt,ContactEdge.forwardEdge,reverseEdge]
  right_inv p := by
    obtain ⟨e,flip⟩ := p
    cases flip <;> apply Prod.ext
    · exact physicalEdge_forwardEdge e
    · simp [sourceProbeSide,ContactEdge.forwardEdge,not_lt_of_ge e.property.1.le]
    · exact physicalEdge_reverse_forwardEdge e
    · simp [sourceProbeSide,ContactEdge.forwardEdge,reverseEdge,e.property.1]

theorem OrientedEdge.exists_contact_orientation {n : ℕ} {G : PennyGraph n} (e : OrientedEdge G) :
    ∃ p : ContactEdge G, e = p.forwardEdge ∨ e = reverseEdge p.forwardEdge := by
  refine ⟨physicalEdge e,?_⟩
  by_cases h : e.val.1 < e.val.2
  · left
    apply Subtype.ext
    simp [physicalEdge,ContactEdge.forwardEdge,h]
  · right
    apply Subtype.ext
    simp [physicalEdge,ContactEdge.forwardEdge,h,reverseEdge]

theorem PennyGraph.sum_orientedEdges_eq_contacts {n : ℕ} (G : PennyGraph n)
    {A : Type*} [AddCommMonoid A] (weight : OrientedEdge G → A) :
    (∑ e : OrientedEdge G, weight e) =
      ∑ e : ContactEdge G, (weight e.forwardEdge+weight (reverseEdge e.forwardEdge)) := by
  calc
    _ = ∑ p : ContactEdge G × Bool, weight (G.orientedPhysicalEquiv.symm p) :=
      Fintype.sum_equiv G.orientedPhysicalEquiv _ _ (by intro e; rw [Equiv.symm_apply_apply])
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro e _
      change (∑ flip : Bool, weight (if flip then reverseEdge e.forwardEdge else e.forwardEdge)) = _
      simp [add_comm]

theorem PennyGraph.face_dart_curl_eq_incidence_sum {n : ℕ} (G : PennyGraph n)
    {A : Type*} [AddCommGroup A] [Module ℝ A] (F : PlaneFace G)
    (weight : OrientedEdge G → A) (hreverse : ∀ e, weight (reverseEdge e) = -weight e) :
    (∑ e ∈ G.faceIncidentDarts F, weight e) =
      ∑ e : ContactEdge G, G.faceIncidence F e • weight e.forwardEdge := by
  rw [PennyGraph.faceIncidentDarts,Finset.sum_filter]
  rw [G.sum_orientedEdges_eq_contacts]
  apply Finset.sum_congr rfl
  intro e _
  rw [hreverse]
  simp only [PennyGraph.faceIncidence,sub_smul,ite_smul,one_smul,zero_smul]
  split_ifs <;> simp

theorem PennyGraph.face_incident_vertex_difference_sum {n : ℕ} (G : PennyGraph n)
    {A : Type*} [AddCommGroup A] (F : PlaneFace G) (f : Fin n → A) :
    (∑ e ∈ G.faceIncidentDarts F, (f e.val.2-f e.val.1)) = 0 := by
  have h := G.sum_faceBoundaryPredecessor F (fun e => f e.val.2)
  simp only [G.faceBoundaryPredecessor_end] at h
  rw [Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr h.symm

end Swanepoel
