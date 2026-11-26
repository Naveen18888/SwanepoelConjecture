module
public import Swanepoel.FaceBoundaryPermutationCircle
public import Swanepoel.SemicirclePorts
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev VertexRay {n : ℕ} (G : PennyGraph n) (v : Fin n) :=
  {w : Fin n // G.graph.Adj v w}

noncomputable instance vertexRayFintype {n : ℕ} (G : PennyGraph n) (v : Fin n) :
    Fintype (VertexRay G v) := Fintype.ofFinite _

def PennyGraph.vertexDirection {n : ℕ} (G : PennyGraph n) (v : Fin n) (a : VertexRay G v) : Plane :=
  G.point a.val-G.point v

theorem PennyGraph.vertexDirection_norm {n : ℕ} (G : PennyGraph n) (v : Fin n) (a : VertexRay G v) :
    ‖G.vertexDirection v a‖=1 := by
  simpa only [PennyGraph.vertexDirection,← dist_eq_norm] using a.property.symm.2

theorem PennyGraph.vertexDirection_injective {n : ℕ} (G : PennyGraph n) (v : Fin n) :
    Function.Injective (G.vertexDirection v) := by
  intro a b h
  apply Subtype.ext
  apply G.point_injective
  simpa only [PennyGraph.vertexDirection,sub_add_cancel] using
    congrArg (fun x : Plane => x+G.point v) h

def PennyGraph.vertexRayRotation {n : ℕ} (G : PennyGraph n) (v : Fin n) : Equiv.Perm (VertexRay G v) :=
  clockwiseRayPermutation (G.vertexDirection v) (G.vertexDirection_norm v) (G.vertexDirection_injective v)

theorem PennyGraph.empty_clockwise_ray_face {n : ℕ} (G : PennyGraph n) (v : Fin n)
    (a b : VertexRay G v)
    (hgap : ∀ c : VertexRay G v,
      ¬ClockwiseRayBetween (G.vertexDirection v a) (G.vertexDirection v b) (G.vertexDirection v c)) :
    G.sourceFace ⟨(v,a.val),a.property⟩ =
      G.sourceFace (reverseEdge ⟨(v,b.val),b.property⟩) := by
  by_cases heq : a=b
  · subst b
    apply G.degree_one_incident_faces_eq v a.val a.property
    intro c hc
    have hdir : G.vertexDirection v ⟨c,hc⟩=G.vertexDirection v a := by
      by_contra hne
      apply hgap ⟨c,hc⟩
      simpa [ClockwiseRayBetween] using hne
    exact congrArg Subtype.val (G.vertexDirection_injective v hdir)
  have hne : G.vertexDirection v a≠G.vertexDirection v b :=
    fun h => heq (G.vertexDirection_injective v h)
  rcases lt_trichotomy (cross2 (G.vertexDirection v a) (G.vertexDirection v b)) 0 with hneg | hzero | hpos
  · apply G.empty_clockwise_sector_face v a.val b.val a.property b.property hneg
    intro c hc hbetween
    apply hgap ⟨c,hc⟩
    simp only [ClockwiseRayBetween,ite_eq_right hne,ite_eq_left hneg]
    simpa only [PennyGraph.vertexDirection] using hbetween
  · have hopp : G.vertexDirection v b= -G.vertexDirection v a :=
      (unit_cross_zero_eq_or_neg _ _ (G.vertexDirection_norm v a) (G.vertexDirection_norm v b) hzero).resolve_left
        (fun h => hne h.symm)
    apply G.empty_antipodal_sector_face v a.val b.val a.property b.property hopp
    intro c hc hright
    apply hgap ⟨c,hc⟩
    simp only [ClockwiseRayBetween,ite_eq_right hne,
      ite_eq_right (not_lt_of_ge hzero.ge),ite_eq_left hzero]
    simpa only [PennyGraph.vertexDirection] using hright
  · apply G.empty_reflex_sector_face v a.val b.val a.property b.property hpos
    · intro c hc hright
      apply hgap ⟨c,hc⟩
      simp only [ClockwiseRayBetween,ite_eq_right hne,ite_eq_right (not_lt_of_ge hpos.le),
        ite_eq_right (ne_of_gt hpos)]
      exact Or.inl hright
    · intro c hc hleft
      apply hgap ⟨c,hc⟩
      simp only [ClockwiseRayBetween,ite_eq_right hne,ite_eq_right (not_lt_of_ge hpos.le),
        ite_eq_right (ne_of_gt hpos)]
      exact Or.inr hleft

theorem PennyGraph.vertexRayRotation_face {n : ℕ} (G : PennyGraph n) (v : Fin n)
    (a : VertexRay G v) :
    G.sourceFace ⟨(v,a.val),a.property⟩ =
      G.sourceFace (reverseEdge ⟨(v,(G.vertexRayRotation v a).val),(G.vertexRayRotation v a).property⟩) := by
  apply G.empty_clockwise_ray_face
  exact clockwiseRayPermutation_empty (G.vertexDirection v) (G.vertexDirection_norm v)
    (G.vertexDirection_injective v) a

def PennyGraph.edgeVertexRayEquiv {n : ℕ} (G : PennyGraph n) :
    OrientedEdge G ≃ Σ v : Fin n, VertexRay G v where
  toFun e := ⟨e.val.1,⟨e.val.2,e.property⟩⟩
  invFun d := ⟨(d.1,d.2.val),d.2.property⟩
  left_inv e := by apply Subtype.ext; rfl
  right_inv d := by rcases d with ⟨v,a⟩; rfl

def PennyGraph.edgeVertexRotation {n : ℕ} (G : PennyGraph n) : Equiv.Perm (OrientedEdge G) :=
  ((G.edgeVertexRayEquiv).trans (Equiv.sigmaCongrRight (fun v => G.vertexRayRotation v))).trans
    (G.edgeVertexRayEquiv).symm

def PennyGraph.edgeReversePermutation {n : ℕ} (G : PennyGraph n) : Equiv.Perm (OrientedEdge G) where
  toFun := reverseEdge
  invFun := reverseEdge
  left_inv := reverseEdge_involutive
  right_inv := reverseEdge_involutive

def PennyGraph.faceBoundaryPredecessor {n : ℕ} (G : PennyGraph n) : Equiv.Perm (OrientedEdge G) :=
  (G.edgeVertexRotation).trans (G.edgeReversePermutation)

@[simp] theorem PennyGraph.faceBoundaryPredecessor_end {n : ℕ} (G : PennyGraph n)
    (e : OrientedEdge G) : (G.faceBoundaryPredecessor e).val.2=e.val.1 := rfl

theorem PennyGraph.faceBoundaryPredecessor_face {n : ℕ} (G : PennyGraph n)
    (e : OrientedEdge G) : G.sourceFace (G.faceBoundaryPredecessor e)=G.sourceFace e :=
  (G.vertexRayRotation_face e.val.1 ⟨e.val.2,e.property⟩).symm

def PennyGraph.faceBoundarySuccessor {n : ℕ} (G : PennyGraph n) : Equiv.Perm (OrientedEdge G) :=
  G.faceBoundaryPredecessor.symm

@[simp] theorem PennyGraph.faceBoundarySuccessor_start {n : ℕ} (G : PennyGraph n)
    (e : OrientedEdge G) : (G.faceBoundarySuccessor e).val.1=e.val.2 := by
  have h := G.faceBoundaryPredecessor_end (G.faceBoundaryPredecessor.symm e)
  rw [G.faceBoundaryPredecessor.apply_symm_apply] at h
  exact h.symm

theorem PennyGraph.faceBoundarySuccessor_face {n : ℕ} (G : PennyGraph n)
    (e : OrientedEdge G) : G.sourceFace (G.faceBoundarySuccessor e)=G.sourceFace e := by
  have h := G.faceBoundaryPredecessor_face (G.faceBoundaryPredecessor.symm e)
  rw [G.faceBoundaryPredecessor.apply_symm_apply] at h
  exact h.symm

def PennyGraph.faceIncidentDarts {n : ℕ} (G : PennyGraph n) (F : PlaneFace G) : Finset (OrientedEdge G) :=
  Finset.univ.filter (fun e => G.sourceFace e=F)

theorem PennyGraph.mem_faceIncidentDarts_predecessor {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) (e : OrientedEdge G) :
    G.faceBoundaryPredecessor e∈G.faceIncidentDarts F ↔ e∈G.faceIncidentDarts F := by
  simp only [PennyGraph.faceIncidentDarts,Finset.mem_filter,Finset.mem_univ,true_and,
    G.faceBoundaryPredecessor_face]

theorem PennyGraph.sum_faceBoundaryPredecessor {n : ℕ} (G : PennyGraph n) (F : PlaneFace G)
    {A : Type*} [AddCommMonoid A] (weight : OrientedEdge G → A) :
    (∑ e ∈ G.faceIncidentDarts F, weight (G.faceBoundaryPredecessor e)) =
      ∑ e ∈ G.faceIncidentDarts F, weight e := by
  refine Finset.sum_bij (fun e _ => G.faceBoundaryPredecessor e) ?_ ?_ ?_ ?_
  · intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (G.faceBoundaryPredecessor_face e).trans (Finset.mem_filter.mp he).2⟩
  · intro e _ f _ h
    exact G.faceBoundaryPredecessor.injective h
  · intro f hf
    refine ⟨G.faceBoundaryPredecessor.symm f,?_,G.faceBoundaryPredecessor.apply_symm_apply f⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    have hface := G.faceBoundaryPredecessor_face (G.faceBoundaryPredecessor.symm f)
    rw [G.faceBoundaryPredecessor.apply_symm_apply] at hface
    exact hface.symm.trans (Finset.mem_filter.mp hf).2
  · intro e _
    rfl

theorem PennyGraph.face_incidence_balance {n : ℕ} (G : PennyGraph n) (F : PlaneFace G) (v : Fin n) :
    ((G.faceIncidentDarts F).filter (fun e => e.val.1=v)).card =
      ((G.faceIncidentDarts F).filter (fun e => e.val.2=v)).card := by
  refine Finset.card_bij (fun e _ => G.faceBoundaryPredecessor e) ?_ ?_ ?_
  · intro e he
    have he' := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr
      ⟨(G.mem_faceIncidentDarts_predecessor F e).mpr he'.1,
        (G.faceBoundaryPredecessor_end e).trans he'.2⟩
  · intro e _ f _ h
    exact G.faceBoundaryPredecessor.injective h
  · intro f hf
    have hf' := Finset.mem_filter.mp hf
    refine ⟨G.faceBoundaryPredecessor.symm f,?_,G.faceBoundaryPredecessor.apply_symm_apply f⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply (G.mem_faceIncidentDarts_predecessor F (G.faceBoundaryPredecessor.symm f)).mp
      rw [G.faceBoundaryPredecessor.apply_symm_apply]
      exact hf'.1
    · have h := G.faceBoundaryPredecessor_end (G.faceBoundaryPredecessor.symm f)
      rw [G.faceBoundaryPredecessor.apply_symm_apply] at h
      exact h.symm.trans hf'.2

theorem PennyGraph.face_incident_carried_sum {n : ℕ} (G : PennyGraph n) (F : PlaneFace G) :
    (∑ e ∈ G.faceIncidentDarts F, carriedVector e)=0 := by
  have h := G.sum_faceBoundaryPredecessor F (fun e => G.point e.val.2)
  simp only [G.faceBoundaryPredecessor_end] at h
  change (∑ e ∈ G.faceIncidentDarts F, (G.point e.val.2-G.point e.val.1))=0
  rw [Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr h.symm

theorem PennyGraph.face_incident_normal_sum {n : ℕ} (G : PennyGraph n) (F : PlaneFace G) :
    (∑ e ∈ G.faceIncidentDarts F, sourceNormal e)=0 := by
  simp only [← rightNormalMap_carriedVector]
  rw [← map_sum,G.face_incident_carried_sum F,map_zero]

theorem PennyGraph.defect_all_source_normals_sum {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (hF : F∈G.defectPlaneFaces ht) :
    (∑ e ∈ G.faceSourcePorts F, sourceNormal e)=0 := by
  rw [G.defect_faceSourcePorts_eq_incident ht F hF]
  exact G.face_incident_normal_sum F

end Swanepoel
